module

public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Frame
public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Bridges
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeStepTwo
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType
open CFSG.GGQ2Prime (le_twoLocalPrimeRank lieModel_PSU_five U52OrderThreeAutInner)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotAutHom (L : Type*) [Group L] : MulAut L →* MulAut (L ⧸ center L) where
  toFun := quotAut
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H y => simp [quotAut_mk]
  map_mul' α β := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H y => simp [quotAut_mk, MulAut.mul_apply]
theorem le_centralizer_of_rank {L : Subgroup G} (hperf : commutator L = ⊤) {M : Type} [Group M]
    (e : (L ⧸ center L) ≃* M)
    {r : ℕ} (hrank : ∀ E P : Subgroup (MulAut M), IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      IsPGroup 2 P → E ≤ normalizer (P : Set _) → P = ⊥)
    {B T : Subgroup G} (hBab : IsElemAbelian 3 B) (hBL : B ≤ normalizer (L : Set G))
    (hB81 : 3 ^ (r + 1) ≤ Nat.card B)
    (hcyc : ∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S)
    (hT2 : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G)) (hBT : B ≤ normalizer (T : Set G)) :
    T ≤ centralizer (L : Set G) := by
  set Nn : Subgroup G := normalizer (L : Set G) with hNn
  let ψ : Nn →* MulAut M :=
    (MulAut.congr e).toMonoidHom.comp ((quotAutHom L).comp (conjHom Nn L le_rfl))
  have hker : ∀ g : Nn, ψ g = 1 → (g : G) ∈ centralizer (L : Set G) := by
    intro g hg
    have h1 : quotAutHom L (conjHom Nn L le_rfl g) = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one]
      exact hg
    have hfix := eq_of_mul_inv_mem_center hperf (conjHom Nn L le_rfl g) (fun y => by
      have := congrArg (fun φ : MulAut (L ⧸ center L) => φ (y : L ⧸ center L)) h1
      simp only [quotAutHom, MonoidHom.coe_mk, OneHom.coe_mk, quotAut_mk, MulAut.one_apply] at this
      rw [← div_eq_mul_inv]
      exact (QuotientGroup.eq_iff_div_mem).1 this)
    rw [mem_centralizer_iff]
    intro y hy
    have := congrArg Subtype.val (hfix ⟨y, hy⟩)
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk] at this
    calc y * g = (g * y * (g : G)⁻¹) * g := by rw [this]
      _ = g * y := by group
  set E : Subgroup (MulAut M) := (B.subgroupOf Nn).map ψ with hE
  set P : Subgroup (MulAut M) := (T.subgroupOf Nn).map ψ with hP
  have hEab : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := mem_map.1 a.2
      obtain ⟨b', hb', hb⟩ := mem_map.1 b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← ha, ← hb, ← map_mul]
      congr 1
      apply Subtype.ext
      have hc := hBab.1.1.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      simpa using congrArg Subtype.val hc
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_map.1 hy
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hBab.2 _ (mem_subgroupOf.1 ha))
      rw [this, map_one]
  have hPp : IsPGroup 2 P := by
    refine IsPGroup.map (fun g => ?_) ψ
    obtain ⟨k, hk⟩ := hT2 ⟨g, mem_subgroupOf.1 g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hEP : E ≤ normalizer (P : Set (MulAut M)) := by
    refine le_trans (map_mono ?_) (le_normalizer_map ψ)
    intro a ha
    rw [mem_normalizer_iff]
    intro c
    simp only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (mem_normalizer_iff.1 (hBT (mem_subgroupOf.1 ha)) c)
  have hE27 : 3 ^ r ≤ Nat.card E := by
    let ψB := ψ.comp (B.subgroupOf Nn).subtype
    have hrange : ψB.range = E := by rw [MonoidHom.range_comp, range_subtype]
    have hprod := card_ker_mul_card_range ψB
    rw [hrange, Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv] at hprod
    set S : Subgroup G := B ⊓ centralizer (L : Set G)
    have hS3 : Nat.card S ≤ 3 := by
      have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hBab.2 _ g.2.1)⟩
      have := hcyc S inf_le_right hSp
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd (by norm_num) (Monoid.exponent_dvd_of_forall_pow_eq_one
        fun g => Subtype.ext (by simpa using hBab.2 _ g.2.1))
    have hk : Nat.card ψB.ker ≤ 3 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun k : ψB.ker => (⟨((k : B.subgroupOf Nn) : Nn), mem_subgroupOf.1 (k : B.subgroupOf Nn).2,
          hker _ k.2⟩ : S)) ?_) hS3
      intro k₁ k₂ h
      exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
    have h1 := Nat.mul_le_mul_right (Nat.card E) hk
    have h2 : 3 * 3 ^ r ≤ 3 * Nat.card E := by
      calc 3 * 3 ^ r = 3 ^ (r + 1) := by ring
        _ ≤ Nat.card B := hB81
        _ = _ := hprod.symm
        _ ≤ 3 * Nat.card E := h1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hPbot := hrank E P hEab hE27 hPp hEP
  intro t ht
  have hmem : ψ ⟨t, hTL ht⟩ ∈ P := mem_map.2 ⟨⟨t, hTL ht⟩, mem_subgroupOf.2 ht, rfl⟩
  rw [hPbot, mem_bot] at hmem
  exact hker _ hmem
@[expose] def U52AutRankInput : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 →
    ∀ E P : Subgroup (MulAut (StatedProj (StatedSU 5 (2 ^ 1) K))), IsElemAbelian 3 E →
      3 ^ 4 ≤ Nat.card E → IsPGroup 2 P → E ≤ normalizer (P : Set _) → P = ⊥

theorem cor_9_4_rank (hU : U52OrderThreeAutInner) (hM : U52MultiplierTrivial)
    (hW : U52NoncyclicPair) (hR : U52AutRankInput) {B L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hL : LieModel (L ⧸ center L) .PSU 5 2 1) :
    twoLocalPrimeRank 3 G ≤ 4 := by
  by_contra h5
  push Not at h5
  obtain ⟨hBab, hxB, hx1, hLc, hcyc, hperf, hBL, T, hTx, hT2, hBT, hTB⟩ := CFSG.GGQ2Prime.ggThmIHyp_unpack hG
  obtain ⟨-, -, -, -, -, -, ⟨⟨-, hBcard, -⟩, -⟩, -⟩ := hG
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five hL
  have hB : 3 ^ (4 + 1) ≤ Nat.card B := by
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) h5
  have hstep3 : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ normalizer (L : Set G) →
      B ≤ normalizer (T : Set G) → T ≤ centralizer (L : Set G) := fun T hT2 hTL hBT =>
    le_centralizer_of_rank hperf e (r := 4) (hR K hF hfin hK) hBab hBL hB hcyc hT2 hTL hBT
  have hcomm := lemma_9_2 hBab hxB hx1 hLc hcyc (bridge_noncyclic_U52 hM hW L hperf hL)
    (fun b hb => bridge_inner_U52 hU L hperf hL (hBL hb) (hBab.2 b hb))
    (bridge_center_U52 hM L hperf hL) hstep3 T hT2 hTx hBT
  apply hTB
  rw [eq_bot_iff, commutator_le]
  intro t ht b hb
  rw [mem_bot, commutatorElement_def, ← hcomm b hb t ht]
  group
theorem exists_two_subgroup_of_even_center {G₁ E : Subgroup G} (hE : E ≤ normalizer (G₁ : Set G))
    (hev : 2 ∣ Nat.card (center G₁)) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ normalizer (U : Set G) := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G₁) 2 hev
  set z' : G := ((z : G₁) : G) with hz'
  set S : Set G := Set.range fun b : E => (b : G) * z' * (b : G)⁻¹ with hS
  have hz2 : z' ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa [hz'] using congrArg (fun w : center G₁ => ((w : G₁) : G)) this
  have hzc : ∀ g ∈ G₁, z' * g = g * z' := by
    intro g hg
    have := mem_center_iff.1 z.2 ⟨g, hg⟩
    exact (congrArg Subtype.val this).symm
  have hSG : ∀ s ∈ S, s ∈ G₁ ∧ (∀ g ∈ G₁, s * g = g * s) ∧ s ^ 2 = 1 := by
    rintro _ ⟨b, rfl⟩
    refine ⟨(mem_normalizer_iff.1 (hE b.2) z').1 (z : G₁).2, fun g hg => ?_, ?_⟩
    · have hg' : (b : G)⁻¹ * g * b ∈ G₁ := by
        have := (mem_normalizer_iff.1 (hE (inv_mem b.2)) g).1 hg
        simpa using this
      have hc := hzc _ hg'
      calc (b : G) * z' * (b : G)⁻¹ * g = b * (z' * ((b : G)⁻¹ * g * b)) * (b : G)⁻¹ := by group
        _ = b * (((b : G)⁻¹ * g * b) * z') * (b : G)⁻¹ := by rw [hc]
        _ = g * ((b : G) * z' * (b : G)⁻¹) := by group
    · rw [show ((b : G) * z' * (b : G)⁻¹) ^ 2 = b * z' ^ 2 * (b : G)⁻¹ by rw [sq, sq]; group, hz2]
      group
  refine ⟨closure S, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : z' ∈ closure S := subset_closure ⟨1, by simp⟩
    rw [hbot, mem_bot] at hmem
    have h1 : z = 1 := Subtype.ext (Subtype.ext hmem)
    rw [h1, orderOf_one] at hz
    norm_num at hz
  · have hk : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
      ((hSG a ha).2.1 b (hSG b hb).1)
    have hsq : ∀ g ∈ closure S, g ^ 2 = 1 := by
      letI : CommGroup (closure S) :=
        closureCommGroupOfComm (fun a ha b hb _ => (hk a ha b hb : Commute a b))
      have htop : closure (((↑) : closure S → G) ⁻¹' S) ≤ (powMonoidHom 2 : closure S →* closure S).ker := by
        rw [closure_le]
        rintro ⟨g, hg⟩ hg'
        ext
        simpa using (hSG g hg').2.2
      rw [closure_closure_coe_preimage] at htop
      intro g hg
      have := htop (mem_top ⟨g, hg⟩)
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
      exact congrArg Subtype.val this
    exact fun g => ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩
  · intro b hb
    apply CFSG.GGQ2Prime.mem_normalizer_of_conj_mem
    intro u hu
    induction hu using closure_induction with
    | mem s hs =>
      obtain ⟨c, rfl⟩ := hs
      exact subset_closure ⟨⟨b * c, mul_mem hb c.2⟩, by simp only [mul_inv_rev]; group⟩
    | one => simp
    | mul u v _ _ hu hv =>
      rw [show b * (u * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) by group]
      exact mul_mem hu hv
    | inv u _ hu =>
      rw [show b * u⁻¹ * b⁻¹ = (b * u * b⁻¹)⁻¹ by group]
      exact inv_mem hu

theorem cor_9_4 (hU : U52OrderThreeAutInner) (hM : U52MultiplierTrivial)
    (hW : U52NoncyclicPair) (hR : U52AutRankInput) {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) (h5 : Nat.card Bs = 3 ^ 5)
    (hL : LieModel (L ⧸ center L) .PSU 5 2 1) (G₁ : Subgroup G)
    (hG₁ : Bs ≤ normalizer (G₁ : Set G)) : Odd (Nat.card (center G₁)) := by
  by_contra hodd
  have hev : 2 ∣ Nat.card (center G₁) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨U, hU1, hU2, hBU⟩ := exists_two_subgroup_of_even_center hG₁ hev
  have h := le_twoLocalPrimeRank (by norm_num) U Bs hU1 hU2 hBU hBs.2.1 h5
  have := cor_9_4_rank hU hM hW hR hG hL
  omega
end CFSG.StandardType.QTwo.U5

end
