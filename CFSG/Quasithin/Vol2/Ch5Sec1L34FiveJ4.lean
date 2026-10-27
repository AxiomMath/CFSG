module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4

public section

namespace CFSG.Quasithin.H13.FiveNorm.J4F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam CFSG.Quasithin.J4Rad
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Open (pCoreOf)

theorem index_ne_three_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : 6 < Nat.card G) (K : Subgroup G) : K.index ≠ 3 := by
  intro hK
  have : Finite (G ⧸ K) :=
    Finite.of_surjective (QuotientGroup.mk : G → G ⧸ K) QuotientGroup.mk_surjective
  set φ := MulAction.toPermHom G (G ⧸ K) with hφ
  have hker : φ.ker ≤ K := by
    intro g hg
    have h0 : φ g (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
      rw [MonoidHom.mem_ker.mp hg]
      rfl
    have h2 : φ g (QuotientGroup.mk 1) = QuotientGroup.mk (g * 1) := rfl
    have h1 : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk 1 := by
      rw [← mul_one g, ← h2, h0]
    rw [QuotientGroup.eq, mul_one] at h1
    exact inv_mem_iff.mp h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    have h2 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, ← Subgroup.index, hK] at h2
    norm_num [Nat.factorial] at h2
    omega
  · have hK1 : K = ⊤ := top_le_iff.mp (h ▸ hker)
    rw [hK1, Subgroup.index_top] at hK
    norm_num at hK

theorem card_eq_card_ker_mul_card_map {G G' : Type*} [Group G] [Group G'] [Finite G]
    {f : G →* G'} (hf : Function.Surjective f) {K : Subgroup G} (hK : f.ker ≤ K) :
    Nat.card K = Nat.card f.ker * Nat.card (K.map f) := by
  have : Finite G' := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index K
  have h2 := Subgroup.card_mul_index (K.map f)
  have h3 : (K.map f).index = K.index := by
    rw [← Subgroup.index_comap_of_surjective _ hf, Subgroup.comap_map_eq_self hK]
  have h4 : Nat.card G = Nat.card f.ker * Nat.card G' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, mul_comm]
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h3] at h2
  have h5 : Nat.card K * K.index = Nat.card f.ker * Nat.card (K.map f) * K.index := by
    rw [h1, h4, ← h2, mul_assoc]
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem alt5_le_of_sixty_dvd {K : Subgroup (Equiv.Perm (Fin 5))} (hK : 60 ∣ Nat.card K) :
    alternatingGroup (Fin 5) ≤ K := by
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd : Nat.card K ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card K
  have hmul := Subgroup.card_mul_index K
  rw [h120] at hmul
  obtain ⟨c, hc⟩ := hK
  have hc2 : c ∣ 2 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 60) (by rw [← hc]; simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with rfl | rfl
  · have hidx : K.index = 2 := by
      rw [hc] at hmul
      omega
    rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx]
  · have hidx : K.index = 1 := by
      rw [hc] at hmul
      omega
    rw [Subgroup.index_eq_one.mp hidx]
    exact le_top

theorem noFiveOver_of_sylow {W : Type} [Group W] [Finite W] {P₀ : Subgroup W}
    (hP₀ : IsSylowTwoOf P₀ ⊤)
    (h : ∀ H : Subgroup W, P₀ ≤ H → Nat.card H ≠ 5 * Nat.card P₀) : NoFiveOver W := by
  intro S H hS hSH hcard
  obtain ⟨c, hc⟩ := CFSG.QuasithinUnique.L246C127.exists_conj_of_isSylowTwoOf' hS hP₀
  have hPH : P₀ ≤ H.map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    exact Subgroup.map_mono hSH
  refine h _ hPH ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard, ← hc,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem noFiveOver_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : NoFiveOver W) : NoFiveOver W' := by
  intro S H hS hSH hcard
  refine h _ _ (isSylowTwoOf_map_mulEquiv e.symm hS) (Subgroup.map_mono hSH) ?_
  rw [Subgroup.card_map_of_injective e.symm.injective,
    Subgroup.card_map_of_injective e.symm.injective]
  exact hcard

section Model

theorem false_of_le_Hj
    {Y : Subgroup J} (hPY : P0 ≤ Y) (hYH : Y ≤ Hj)
    (hY : Nat.card Y = 5 * 2 ^ 21) : False := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  set f : ↥Hj →* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    (MulEquiv.subgroupCongr range_starHom_eq).toMonoidHom.comp starHom.rangeRestrict with hf
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr range_starHom_eq).surjective.comp starHom.rangeRestrict_surjective
  have hfk : f.ker = (Eg uJ 11).subgroupOf Hj := by
    rw [← ker_starHom, ← MonoidHom.ker_rangeRestrict starHom]
    ext x
    simp only [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulEquiv.injective _)]
  have hEY : (Eg uJ 11).subgroupOf Hj ≤ Y.subgroupOf Hj :=
    Subgroup.subgroupOf_mono _ (Eg_le_P0.trans hPY)
  have hkcard : Nat.card f.ker = 2 ^ 11 := by
    rw [hfk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).toEquiv]
    exact card_Eg_uJ hM
  have hYc : Nat.card ((Y.subgroupOf Hj).map f) = 5 * 2 ^ 10 := by
    have h1 := card_eq_card_ker_mul_card_map hfs (hfk ▸ hEY)
    rw [hkcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv, hY] at h1
    omega
  have hP0H : IsSylowTwoOf (P0.subgroupOf Hj) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf
      (A4.isSylowTwoOf_mono isSylowTwoOf_P0 P0_le_Hj le_top)
  have hT := isSylowTwoOf_top_map_of_surjective hP0H f hfs
  have hTY : (P0.subgroupOf Hj).map f ≤ (Y.subgroupOf Hj).map f :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hPY)
  rcases CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups
      (X := ↥CFSG.Blueprint.NativeSporadic.M24) ⟨MulEquiv.refl _⟩ hT hTY with
    htop | ⟨r, hr, hr1, -⟩
  · rw [htop, Subgroup.card_top, CFSG.Sporadic.Mathieu.card_M24] at hYc
    norm_num at hYc
  · rw [hYc] at hr1
    simp only [CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hr1

theorem false_of_le_M3
    {Y : Subgroup J} (hPY : P0 ≤ Y) (hYM : Y ≤ M3)
    (hY : Nat.card Y = 5 * 2 ^ 21) : False := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨g, hgY⟩, hg5⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5
    (by rw [hY]; exact dvd_mul_right 5 _)
  have hgo : orderOf g = 5 := by rw [← Subgroup.orderOf_mk g hgY]; exact hg5
  have hg'o : orderOf (⟨g, hYM hgY⟩ : ↥M3) = 5 := by rw [Subgroup.orderOf_mk, hgo]
  have hα : V0.normalizerMonoidHom ⟨g, hYM hgY⟩ = 1 := by
    have h1 := orderOf_map_dvd V0.normalizerMonoidHom (⟨g, hYM hgY⟩ : ↥M3)
    rw [hg'o] at h1
    have h2 := orderOf_dvd_natCard (V0.normalizerMonoidHom ⟨g, hYM hgY⟩)
    rw [card_mulAut_V0 hM] at h2
    have h3 : orderOf (V0.normalizerMonoidHom ⟨g, hYM hgY⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
      · exact h
      · rw [h] at h2
        norm_num at h2
    exact orderOf_eq_one_iff.mp h3
  have hρg : orderOf (rho3 hF ⟨g, hYM hgY⟩) = 5 := by
    have h1 := orderOf_map_dvd (rho3 hF) (⟨g, hYM hgY⟩ : ↥M3)
    rw [hg'o] at h1
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exfalso
      have hmem : (⟨g, hYM hgY⟩ : ↥M3) ∈
          ((rho3 hF).ker ⊓ V0.normalizerMonoidHom.ker : Subgroup ↥M3) :=
        ⟨MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h), MonoidHom.mem_ker.mpr hα⟩
      obtain ⟨k, hk⟩ := isPGroup_ker_rho3_alpha3 hF ⟨_, hmem⟩
      have h2 : (⟨g, hYM hgY⟩ : ↥M3) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hg'o] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
        (Nat.prime_five.dvd_of_dvd_pow h3)
      omega
    · exact h
  have hρgA : rho3 hF ⟨g, hYM hgY⟩ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h0 : rho3 hF ⟨g, hYM hgY⟩ ^ 5 = 1 := by
      have := pow_orderOf_eq_one (rho3 hF ⟨g, hYM hgY⟩)
      rwa [hρg] at this
    have h1 : Equiv.Perm.sign (rho3 hF ⟨g, hYM hgY⟩) ^ 5 = 1 := by
      rw [← map_pow, h0, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (rho3 hF ⟨g, hYM hgY⟩)) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hA5I : alternatingGroup (Fin 5) ≤ (rho3 hF).range := by
    have h1 := alt5_le_of_sixty_dvd (sixty_dvd_card_rho3 hF)
    exact h1.trans (by rw [MonoidHom.range_comp]; exact Subgroup.map_le_range _ _)
  have hA5n : (rho3 hF).range ≤
      Subgroup.normalizer ((alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) :
        Set (Equiv.Perm (Fin 5))) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hP0M : IsSylowTwoOf (P0.subgroupOf M3) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf
      (A4.isSylowTwoOf_mono isSylowTwoOf_P0 (hPY.trans hYM) le_top)
  have hPbI : IsSylowTwoOf ((P0.subgroupOf M3).map (rho3 hF)) (rho3 hF).range := by
    have h1 := isSylowTwoOf_top_map_of_surjective hP0M (rho3 hF).rangeRestrict
      (rho3 hF).rangeRestrict_surjective
    have h2 : (P0.subgroupOf M3).map (rho3 hF).rangeRestrict =
        ((P0.subgroupOf M3).map (rho3 hF)).subgroupOf (rho3 hF).range := by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨m, hm, hmx⟩
        exact ⟨m, hm, congrArg Subtype.val hmx⟩
      · rintro ⟨m, hm, hmx⟩
        exact ⟨m, hm, Subtype.ext hmx⟩
    rw [h2] at h1
    refine ⟨Subgroup.map_le_range _ _, hP0M.2.1.map _, ?_⟩
    have h3 : ((((P0.subgroupOf M3).map (rho3 hF)).subgroupOf (rho3 hF).range).subgroupOf
        ⊤).index = (((P0.subgroupOf M3).map (rho3 hF)).subgroupOf (rho3 hF).range).index :=
      Subgroup.relIndex_top_right _
    have h4 := h1.2.2
    rwa [h3] at h4
  have hPbA : Nat.card ↥((P0.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5)) = 4 := by
    have h1 := A4.isSylowTwoOf_inf_normal hPbI hA5I hA5n
    have h2 := card_eq_of_isSylowTwoOf_top (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf h1)
      (k := 2) (m := 15) (by rw [card_alt5]; norm_num) (by decide)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h2
  have hPbR : (P0.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5) ≤
      (Y.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5) :=
    inf_le_inf_right _ (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hPY))
  have hgR : rho3 hF ⟨g, hYM hgY⟩ ∈
      (Y.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5) :=
    ⟨⟨⟨g, hYM hgY⟩, Subgroup.mem_subgroupOf.mpr hgY, rfl⟩, hρgA⟩
  set n := Nat.card ↥((Y.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5)) with hn
  have h4 : 4 ∣ n := by
    have := Subgroup.card_dvd_of_le hPbR
    rwa [hPbA] at this
  have h5 : 5 ∣ n := by
    have := Subgroup.orderOf_dvd_natCard _ hgR
    rwa [hρg] at this
  have h60 : n ∣ 60 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : (Y.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5) ≤ _)
    rwa [card_alt5] at this
  have hY' : n ∣ 5 * 2 ^ 21 := by
    have h1 : Nat.card ((Y.subgroupOf M3).map (rho3 hF)) ∣ Nat.card ↥(Y.subgroupOf M3) :=
      Subgroup.card_map_dvd _ _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv, hY] at h1
    exact (Subgroup.card_dvd_of_le inf_le_left).trans h1
  have h20 : n = 20 := by
    obtain ⟨c, hc⟩ : 20 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
    have hc3 : c ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 20)
      (by rw [← hc, show (20 : ℕ) * 3 = 60 by norm_num]; exact h60)
    rcases (Nat.dvd_prime Nat.prime_three).mp hc3 with h | h
    · rw [hc, h]
    · exfalso
      rw [hc, h] at hY'
      norm_num at hY'
  have hidx : (((Y.subgroupOf M3).map (rho3 hF) ⊓ alternatingGroup (Fin 5)).subgroupOf
      (alternatingGroup (Fin 5))).index = 3 := by
    have h1 := Subgroup.card_mul_index (((Y.subgroupOf M3).map (rho3 hF) ⊓
      alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, ← hn, h20,
      card_alt5] at h1
    omega
  exact index_ne_three_of_isSimpleGroup (by rw [card_alt5]; norm_num) _ hidx

theorem false_of_P0_le
    {Y : Subgroup J} (hPY : P0 ≤ Y) (hY : Nat.card Y = 5 * 2 ^ 21) : False := by
  have hF : J4Facts := j4Facts
  classical
  have hs : Group.IsSolvable ↥Y := by
    let _ : Fintype ↥Y := Fintype.ofFinite _
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 5) (a := 21) (b := 1) Nat.prime_two Nat.prime_five (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, hY]
    ring
  rcases overgroup_of_solvable hPY hs with h | h | h
  · exact false_of_le_Hj hPY h hY
  · rcases CFSG.Quasithin.J4M2.J4M2Lattice hF hPY h with h' | h' | h'
    · exact false_of_le_Hj hPY h' hY
    · exact false_of_le_M3 hPY h' hY
    · rw [h', CFSG.Quasithin.J4M2.card_M2_two_part hF] at hY
      norm_num at hY
  · exact false_of_le_M3 hPY h hY

theorem noFiveOver_J
    : NoFiveOver J := by
  have hF : J4Facts := j4Facts
  refine noFiveOver_of_sylow isSylowTwoOf_P0 fun Y hPY hY => false_of_P0_le hPY ?_
  rw [hY, card_P0 hF.mat hF]

theorem fiveRigid_J4
    : FiveRigid (CFSG.Blueprint.NativeSporadic.Carrier .J4) := by
  have hF : J4Facts := j4Facts
  obtain ⟨e⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .J4 ≃* J) :=
    ⟨seedEquiv hF.mat⟩
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    fam_j4_simplicity.2.2
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) =
      86775571046077562880 := card_J4
  have hc2 : 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) := by
    rw [hcard]
    norm_num
  have hcne : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) ≠ 2 := by
    rw [hcard]
    norm_num
  have hZ := center_eq_bot_of_card_not_prime
    (W := CFSG.Blueprint.NativeSporadic.Carrier .J4) fun hp =>
      hcne ((hp.eq_one_or_self_of_dvd 2 hc2).resolve_left (by norm_num)).symm
  have hno : NoFiveOver J := noFiveOver_J
  have h1 : NoFiveOver (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    @noFiveOver_of_mulEquiv ↥J _ (Subgroup.toGroup J) _ e.symm hno
  exact ⟨hZ, fun α _ => CFSG.Quasithin.H13.KGInsp.j4_all_inner e α, h1⟩

end Model

end CFSG.Quasithin.H13.FiveNorm.J4F
