module

public import CFSG.Quasithin.Background.SmithB57EC
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Alt
public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222G2
public import CFSG.Quasithin.H13.U3FrameProducer
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.G64SymCase

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC
open scoped commutatorElement

section Commutant

variable {V : Type} [CommGroup V]

theorem fixV_resHom {L : Subgroup (MulAut V)} (hU : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L) :
    fixV (H13.VolI.resHom L (commV L) hU).range =
      (fixV L ⊓ commV L).subgroupOf (commV L) := by
  ext u
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hu
    refine ⟨fun l hl => ?_, u.2⟩
    have h := hu _ ⟨⟨l, hl⟩, rfl⟩
    exact congrArg Subtype.val h
  · rintro ⟨hu, -⟩ g ⟨l, rfl⟩
    exact Subtype.ext (hu _ l.2)

theorem trivial_on_commV_of_move {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (hmove : ∀ (hU : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L) (c : MulAut ↥(commV L)),
      (∀ g ∈ (H13.VolI.resHom L (commV L) hU).range, c * g = g * c) →
      ∃ v, v ∉ fixV (H13.VolI.resHom L (commV L) hU).range ∧
        c v * v⁻¹ ∈ fixV (H13.VolI.resHom L (commV L) hU).range)
    {x : MulAut V} (hxL : ∀ l ∈ L, x * l = l * x) : ∀ u ∈ commV L, x u = u := by
  have hU : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => hI.2.1 ⟨l, hl⟩ u hu
  obtain ⟨-, -, -, hirr⟩ := B5.irr_data hI
  set Γ := (H13.VolI.resHom L (commV L) hU).range with hΓ
  have hconj : ∀ y ∈ L, x * y * x⁻¹ ∈ L := fun y hy => by
    rw [hxL y hy, mul_inv_cancel_right]
    exact hy
  have hconj' : ∀ y ∈ L, x⁻¹ * y * x⁻¹⁻¹ ∈ L := fun y hy => by
    have h := hxL y hy
    have : x⁻¹ * y = y * x⁻¹ := by
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h]
        _ = y * x⁻¹ := by group
    rw [this, inv_inv, inv_mul_cancel_right]
    exact hy
  have hxU : ∀ u ∈ commV L, x u ∈ commV L := fun u hu => FFC.commV_invariant hconj hu
  have hxU' : ∀ u ∈ commV L, x⁻¹ u ∈ commV L := fun u hu => FFC.commV_invariant hconj' hu
  set c := H13.VolI.restrictAut (commV L) x hxU hxU' with hc
  have hcΓ : ∀ g ∈ Γ, c * g = g * c := by
    rintro _ ⟨l, rfl⟩
    ext u
    show x ((l : MulAut V) (u : V)) = (l : MulAut V) (x (u : V))
    exact congrArg (fun φ : MulAut V => φ (u : V)) (hxL l l.2)
  have hirrΓ : ∀ J : Subgroup ↥(commV L), fixV Γ ≤ J → (∀ g ∈ Γ, ∀ w ∈ J, g w ∈ J) →
      J = fixV Γ ∨ J = ⊤ := by
    intro J hJ hJinv
    have hJ' := hirr (J.map (commV L).subtype)
      (by
        rintro l hl _ ⟨w, hw, rfl⟩
        exact ⟨_, hJinv _ ⟨⟨l, hl⟩, rfl⟩ w hw, rfl⟩)
      (by
        intro z hz
        have hz' : (⟨z, hz.1⟩ : ↥(commV L)) ∈ fixV Γ := by
          rw [hΓ, fixV_resHom hU, Subgroup.mem_subgroupOf]
          exact ⟨hz.2, hz.1⟩
        exact ⟨_, hJ hz', rfl⟩)
      (Subgroup.map_subtype_le J)
    rcases hJ' with h | h
    · left
      ext w
      rw [hΓ, fixV_resHom hU, Subgroup.mem_subgroupOf]
      constructor
      · intro hw
        have : (w : V) ∈ J.map (commV L).subtype := ⟨w, hw, rfl⟩
        rw [h] at this
        exact ⟨this.2, this.1⟩
      · intro hw
        have : (w : V) ∈ commV L ⊓ fixV L := ⟨hw.2, hw.1⟩
        rw [← h] at this
        obtain ⟨w', hw', hww⟩ := this
        rw [show w = w' from Subtype.ext hww.symm]
        exact hw'
    · right
      rw [eq_top_iff]
      intro w _
      have : (w : V) ∈ J.map (commV L).subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', hww⟩ := this
      rw [show w = w' from Subtype.ext hww.symm]
      exact hw'
  have hc1 : c = 1 := H13.End1222.eq_one_of_exists
    (H13.VolI.commV_resHom_range hU hI.2.2.1) hirrΓ hcΓ (hmove hU c hcΓ)
  intro u hu
  have := congrArg (fun φ : MulAut ↥(commV L) => ((φ ⟨u, hu⟩ : ↥(commV L)) : V)) hc1
  exact this

theorem trivial_on_commV_alt {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤) {n : ℕ}
    (hn : 5 ≤ n) (hA : AlternatingNatural L (commV L) (fixV L ⊓ commV L) n)
    {x : MulAut V} (hxL : ∀ l ∈ L, x * l = l * x) : ∀ u ∈ commV L, x u = u := by
  refine trivial_on_commV_of_move hI (fun hU c hc => ?_) hxL
  have hR := H13.VolI.realizes_resHom_range hU (FFModel.altDn n) hA
  rw [← fixV_resHom hU] at hR
  exact H13.End1222.AltDn.exists_move_of_altDn hn hR rfl hc

theorem trivial_on_commV_g2 {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (hG : G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1)
    {x : MulAut V} (hxL : ∀ l ∈ L, x * l = l * x) : ∀ u ∈ commV L, x u = u := by
  obtain ⟨K, _, _, hK, hR⟩ := hG
  refine trivial_on_commV_of_move hI (fun hU c hc => ?_) hxL
  have hR' := H13.VolI.realizes_resHom_range hU _ hR
  rw [← fixV_resHom hU] at hR'
  exact H13.End1222.G2.exists_move_of_zornQ (by simpa using hK) hR' rfl hc

end Commutant

section Orders

theorem card_natMod_fintype {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ Fintype.card ι := by
  rw [← Nat.card_congr (MulEquiv.ofBijective (G64.natQuot Γ)
    ⟨G64.natQuot_injective, G64.natQuot_surjective⟩).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

end Orders

variable {V : Type} [CommGroup V] [Finite V]

theorem not_list5 {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hUZ : Nat.card U = 64 * Nat.card Z) (hL8 : Nat.card ↥L ≠ 20160) :
    ¬ B51NaturalList5 L U Z := by
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  rintro (⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩)
  · have h := G64.RealizesVia.card_eq hπ
    rw [card_natMod_fintype, hK, Fintype.card_sum, Fintype.card_fin, hUZ, ← pow_mul] at h
    have h' := Nat.eq_of_mul_eq_mul_right hZpos h
    have h2 : (2 : ℕ) ^ 6 = 2 ^ (n * (2 + 2)) := by simpa using h'
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega
  · have h := G64.RealizesVia.card_eq hπ
    have h6 : Nat.card (FFModel.altDn 6).Mod = 2 ^ 4 := by
      have := G64.card_symDn_mod (n := 6) (by norm_num)
      rw [ite_eq_left_iff.mpr (fun h => absurd (by decide) h)] at this
      exact this
    rw [h6, hUZ] at h
    have h' := Nat.eq_of_mul_eq_mul_right hZpos h
    norm_num at h'
  · have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hb : Function.Bijective π := ⟨hinj, hπ.1⟩
    have hc : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥L :=
      Nat.card_congr (Equiv.ofBijective π hb)
    rw [nat_card_alternatingGroup] at hc
    simp [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial] at hc
    exact hL8 hc.symm
  · have h := G64.RealizesVia.card_eq hπ
    rw [G64.card_natMod, hK, hUZ] at h
    have h' := Nat.eq_of_mul_eq_mul_right hZpos h
    norm_num at h'

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem commute_X_of_sup (hP4 : AsB15Part4) (hUX : ∀ x ∈ pCoreOf 3 G, ∀ u ∈ commV L, x u = u)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    (hsup : commV L ⊔ fixV (L ⊔ B) = ⊤) :
    B ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)) := by
  obtain ⟨-, hinf⟩ := isDirectSum_commV_fixV S.hV G
  intro b hb
  have hbG : b ∈ G := hB.1 hb
  have hbY : ∀ y ∈ commV (pCoreOf 3 G), b y = y := by
    intro y hy
    have hyt : y ∈ commV L ⊔ fixV (L ⊔ B) := by rw [hsup]; exact Subgroup.mem_top y
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hyt
    have hbw : b w = w := hw b ((le_sup_right : B ≤ L ⊔ B) hb)
    have hbu : b u ∈ commV L := FFC.commV_invariant (S.conj_mem hP4 hbG) hu
    have hm1 : b (u * w) * (u * w)⁻¹ ∈ commV L := by
      rw [map_mul, hbw, mul_inv_rev, ← mul_assoc, mul_assoc (b u), mul_inv_cancel, mul_one]
      exact (commV L).mul_mem hbu ((commV L).inv_mem hu)
    have hm2 : b (u * w) * (u * w)⁻¹ ∈ commV (pCoreOf 3 G) := by
      have hconj : ∀ z ∈ pCoreOf 3 G, b * z * b⁻¹ ∈ pCoreOf 3 G := fun z hz =>
        (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCore3 G) hbG) z).1 hz
      exact (commV _).mul_mem (FFC.commV_invariant hconj hy) ((commV _).inv_mem hy)
    have hm3 : b (u * w) * (u * w)⁻¹ ∈ fixV (pCoreOf 3 G) := fun x hx => hUX x hx _ hm1
    have hm : b (u * w) * (u * w)⁻¹ ∈ commV (pCoreOf 3 G) ⊓ fixV (pCoreOf 3 G) := ⟨hm2, hm3⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (S.commute_X_of_trivial_commV hbG hbY x hx).symm


theorem false_of_seven (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    (hBX : ¬ B ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)))
    (hI : commV L ∈ IrrPlus L ⊤)
    (hS : SymmetricNatural (L ⊔ B) (commV L) (fixV L ⊓ commV L) 7) : False := by
  have hcomm := S.commutator_sup hP4 hB
  have hA : AlternatingNatural L (commV L) (fixV L ⊓ commV L) 7 := by
    have := B5.alternatingNatural_derived (by norm_num) hS
    rwa [hcomm] at this
  have hUX : ∀ x ∈ pCoreOf 3 G, ∀ u ∈ commV L, x u = u := fun x hx =>
    trivial_on_commV_alt hI (by norm_num) hA (fun l hl => S.commute_X x hx l hl)
  obtain ⟨π, hπ, -⟩ := S.sym_data hP4 hB (by norm_num) hS
  have hLc : Nat.card ↥L = 2520 := by
    rw [card_eq_alternating (by norm_num) hcomm π, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  have hUZ : Nat.card ↥(commV L) = 64 * Nat.card ↥(fixV L ⊓ commV L) := by
    have h7 : Nat.card (FFModel.symDn 7).Mod = 2 ^ 6 := by
      have := G64.card_symDn_mod (n := 7) (by norm_num)
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))] at this
      exact this
    rw [G64.RealizesVia.card_eq hπ, h7]
    norm_num
  have hconc := hB51 V S.hV (L ⊔ B) L (S.b51Hyp_sup hP4 hA21 hB)
  rcases hconc.2.2.2.2.1 with hsup | ⟨-, hlist, -⟩
  · exact hBX (S.commute_X_of_sup hP4 hUX hB hsup)
  · exact not_list5 hUZ (by rw [hLc]; norm_num) hlist

theorem false_of_g2 (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    (hBX : ¬ B ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)))
    (hI : commV L ∈ IrrPlus L ⊤)
    (hG : G2Natural (L ⊔ B) (commV L) (fixV L ⊓ commV L) 1) : False := by
  have hcomm := S.commutator_sup hP4 hB
  have hGd : G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1 := by
    have := B5.g2NaturalDerived_of_g2Natural hG
    rwa [hcomm] at this
  have hUX : ∀ x ∈ pCoreOf 3 G, ∀ u ∈ commV L, x u = u := fun x hx =>
    trivial_on_commV_g2 hI hGd (fun l hl => S.commute_X x hx l hl)
  obtain ⟨K, _, _, hK, π, hπ⟩ := hG
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have hinj := FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
  have hM : Nat.card ↥(L ⊔ B) = 12096 := by
    have hc : Nat.card ↥(CFSG.Open.quasithinG2 K) = Nat.card ↥(L ⊔ B) :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
    rw [card_quasithinG2_1527d hK, hK2] at hc
    norm_num at hc
    exact hc.symm
  have hLle : Nat.card ↥L ≤ 12096 := hM ▸ Subgroup.card_le_of_le le_sup_left
  have hUZ : Nat.card ↥(commV L) = 64 * Nat.card ↥(fixV L ⊓ commV L) := by
    rw [G64.RealizesVia.card_eq hπ]
    congr 1
    exact H13.U3.card_zornQ_of_card_two hK2
  have hconc := hB51 V S.hV (L ⊔ B) L (S.b51Hyp_sup hP4 hA21 hB)
  rcases hconc.2.2.2.2.1 with hsup | ⟨-, hlist, -⟩
  · exact hBX (S.commute_X_of_sup hP4 hUX hB hsup)
  · exact not_list5 hUZ (by omega) hlist

end Hyp

end SmithB57E

end CFSG.Quasithin
