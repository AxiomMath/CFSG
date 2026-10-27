module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch7Sec77Setup

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable (S : Setup T L I)
include S

theorem isSylowTwoOf_T : IsSylowTwoOf T ⊤ :=
  isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow le_top

theorem pCoreOf_fsuM_le :
    pCoreOf 2 (fsuM T L) ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    have h := S.hQ
    rwa [S.fsuL0_eq] at h
  rw [← hQ]
  refine pCoreOf_le_pCoreOf_of_sylow S.uniq.1.2 S.hyp.fsu.sylow.1 le_sup_right ?_
  intro h2
  exact S.hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le S.T_le_fsuM))

theorem charTwo_fsuM_inf {H : Subgroup G}
    (hQH : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ H) : CharTwo (fsuM T L ⊓ H) := by
  refine charTwo_of_isTwoLocal_of_pCore_centralizer_le S.hyp.fsu.qtke.2.1 S.isSylowTwoOf_T
    S.uniq.1.1.1 S.T_le_fsuM inf_le_left ?_
  intro x hx
  exact ⟨pCoreOf_le 2 _ hx.1, hQH (S.pCoreOf_fsuM_le hx.1)⟩

theorem oddCoreIn_eq_bot {H Vp Vm X : Subgroup G}
    (hQH : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ H) (hH2 : pCoreOf 2 H ≠ ⊥)
    (hHVp : H ≤ Subgroup.centralizer (Vp : Set G)) (hVmV : Vm ≤ fsuV T I) (hVmH : Vm ≤ H)
    (hXH : X ≤ H) (hXo : Odd (Nat.card X)) (hVmX : ⁅Vm, X⁆ = Vm)
    (hA : Subgroup.centralizer (Vp : Set G) ⊓ Subgroup.centralizer (Vm : Set G) ≤ fsuM T L) :
    oddCoreIn H = ⊥ := by
  have hVm2 : IsElemAbelian 2 Vm := B2F.isElemAbelian_mono hVmV S.hV
  have hX : opResidual 2 X = X := by
    refine le_antisymm (opResidual_le 2 _) fun x hx => ?_
    refine mem_opResidual_of_coprime hx ?_
    exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat hXo (Subgroup.orderOf_dvd_natCard X hx))
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p H) ≤ 2 :=
    fun p hp hp2 => (CFSG.SectionRank.pRank_mono hp.one_lt (pCoreOf_le p H)).trans
      (pRank_le_two_of_pCoreOf_ne_bot S.hyp.fsu.qtke hH2 hp hp2)
  have hcent : Vm ≤ Subgroup.centralizer (fusionOddCoreOf H : Set G) :=
    a126_one hXH hX hVmH (B2F.isPGroup_of_isElemAbelian hVm2) hVmX hrank
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hVm2)
  have hOM : oddCoreIn H ≤ fsuM T L ⊓ H := by
    intro y hy
    have hyH : y ∈ H := Subgroup.map_subtype_le _ hy
    refine ⟨hA ⟨hHVp hyH, ?_⟩, hyH⟩
    change y ∈ Subgroup.centralizer (Vm : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hcent hv) y hy).symm
  have h := oddCoreIn_inf_eq_bot (S.charTwo_fsuM_inf hQH) inf_le_right
  rwa [inf_eq_left.mpr hOM] at h

theorem not_le_of_isComponentIn {H K : Subgroup G}
    (hQH : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ H) (hK : IsComponentIn K H) :
    ¬ K ≤ fsuM T L := fun hKM =>
  DoubleA3.not_isComponentIn_of_charTwo (S.charTwo_fsuM_inf hQH) K
    (BenderBranch.isComponentIn_of_le hK (le_inf hKM hK.1) inf_le_right)

theorem oTwoUpper_le_normalizer (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {H K : Subgroup G} (hH2 : pCoreOf 2 H ≠ ⊥)
    (hK : IsComponentIn K H) : oTwoUpper H ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke).1
  rcases Vol2Native.lemma_1_2_1_three hloc h37c h38c hH2
      (Vol2Native.mem_cComp_of_isComponentIn hK) with
    hn | ⟨h2, -⟩
  · exact (oTwoUpper_le H).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mp hn)
  ·
    have hidx : ((Subgroup.normalizer (K : Set G)).subgroupOf H).index = 2 := by
      rw [← A5.ncard_conjSubgroupsBy_eq_index]
      exact h2
    have hn : ((Subgroup.normalizer (K : Set G)).subgroupOf H).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxo⟩
    set q := (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) :
      ↥H ⧸ (Subgroup.normalizer (K : Set G)).subgroupOf H) with hq
    have hq1 : orderOf q ∣ 2 := by
      rw [← hidx, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard q
    have hq2 : orderOf q ∣ orderOf x := by
      have h1 : orderOf q ∣ orderOf (⟨x, hxH⟩ : ↥H) :=
        orderOf_map_dvd (QuotientGroup.mk' ((Subgroup.normalizer (K : Set G)).subgroupOf H)) _
      rwa [Subgroup.orderOf_mk] at h1
    have hq3 : orderOf q = 1 := by
      have h1 := Nat.dvd_gcd hq1 hq2
      have h2 : Nat.gcd 2 (orderOf x) = 1 := Nat.coprime_two_left.mpr hxo
      rw [h2] at h1
      exact Nat.dvd_one.mp h1
    rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff] at hq3
    exact hq3

omit S [Finite G] in
theorem isSylowTwoOf_map_of_injective {f : G →* G} (hf : Function.Injective f) {P H : Subgroup G}
    (h : IsSylowTwoOf P H) : IsSylowTwoOf (P.map f) (H.map f) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, ?_⟩
  have h1 : ((P.map f).subgroupOf (H.map f)).index = (P.subgroupOf H).index :=
    Subgroup.relIndex_map_map_of_injective P H hf
  rw [h1]
  exact h.2.2

omit S [Finite G] in
theorem isSylowTwoOf_of_odd {P K H : Subgroup G} (hP : IsSylowTwoOf P K) (hKH : K ≤ H)
    (hodd : ¬ 2 ∣ K.relIndex H) : IsSylowTwoOf P H := by
  refine ⟨hP.1.trans hKH, hP.2.1, fun h2 => ?_⟩
  have h := Subgroup.relIndex_mul_relIndex P K H hP.1 hKH
  have h2' : 2 ∣ P.relIndex H := h2
  rw [← h] at h2'
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2' with h' | h'
  · exact hP.2.2 h'
  · exact hodd h'

theorem exists_conj_sylow (h3104 : Stmt3_2_10_four) {U : Subgroup G} (hUV : U ≤ fsuV T I) :
    ∃ m ∈ fsuM T L,
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) :
          Set G)) (Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) :
          Set G)) ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) :
          Set G)) (fsuM T L ⊓ Subgroup.centralizer
          ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : ⊥ ≤ fsuM T L ⊓
    Subgroup.normalizer (U : Set G)) IsPGroup.of_bot
  obtain ⟨S', hS', hPS'⟩ := A4.exists_isSylowTwoOf_ge (hP.1.trans inf_le_left) hP.2.1
  have hTM : IsSylowTwoOf T (fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow S.T_le_fsuM
  obtain ⟨h, hhM, hhS⟩ := A4.exists_conj_of_isSylowTwoOf hTM hS'
  refine ⟨h⁻¹, (fsuM T L).inv_mem hhM, ?_⟩
  set U' := U.map (MulAut.conj h⁻¹).toMonoidHom with hU'
  set P' := P.map (MulAut.conj h⁻¹).toMonoidHom with hP'
  have hP'T : P' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hhS x).mp (hPS' hx)
    simpa [MulAut.conj_apply] using this
  have hMconj : (fsuM T L).map (MulAut.conj h⁻¹).toMonoidHom = fsuM T L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ((fsuM T L).inv_mem hhM))
  have hNconj : (Subgroup.normalizer (U : Set G)).map (MulAut.conj h⁻¹).toMonoidHom =
      Subgroup.normalizer (U' : Set G) := Subgroup.map_equiv_normalizer_eq U (MulAut.conj h⁻¹)
  have hNM : (fsuM T L ⊓ Subgroup.normalizer (U : Set G)).map (MulAut.conj h⁻¹).toMonoidHom =
      fsuM T L ⊓ Subgroup.normalizer (U' : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj h⁻¹).injective, hMconj, hNconj]
  have hP'S : IsSylowTwoOf P' (fsuM T L ⊓ Subgroup.normalizer (U' : Set G)) := by
    rw [← hNM]
    exact isSylowTwoOf_map_of_injective (MulAut.conj h⁻¹).injective hP
  have hTN : IsSylowTwoOf (T ⊓ Subgroup.normalizer (U' : Set G))
      (fsuM T L ⊓ Subgroup.normalizer (U' : Set G)) := by
    have hle : P' ≤ T ⊓ Subgroup.normalizer (U' : Set G) := le_inf hP'T (hP'S.1.trans inf_le_right)
    have h2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (U' : Set G)) :=
      S.hyp.fsu.sylow.1.to_le inf_le_left
    have hle' : T ⊓ Subgroup.normalizer (U' : Set G) ≤
        fsuM T L ⊓ Subgroup.normalizer (U' : Set G) :=
      inf_le_inf_right _ S.T_le_fsuM
    have heq := ((A4.isSylowTwoOf_iff_maximal.mp hP'S).2.2 _ hle' h2 hle).antisymm hle
    rw [heq]
    exact hP'S
  have hU'V : U' ≤ fsuV T I := by
    rintro _ ⟨u, hu, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (S.hMN ((fsuM T L).inv_mem hhM)) u).mp (hUV hu)
    simpa [MulAut.conj_apply] using this
  have hVp : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 S.hL, rfl⟩
  have hodd := h3104 G T L I (fsuV T I) S.hyp.fsu hVp S.hJ U' hU'V
  have hTG : IsSylowTwoOf (T ⊓ Subgroup.normalizer (U' : Set G))
      (Subgroup.normalizer (U' : Set G)) := isSylowTwoOf_of_odd hTN inf_le_right hodd
  have hCN : Subgroup.centralizer (U' : Set G) ≤ Subgroup.normalizer (U' : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCnorm : Subgroup.normalizer (U' : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U' : Set G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hy u hu
      have hu' : x⁻¹ * u * x ∈ U' := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) u).mp hu
        simpa [mul_assoc] using this
      have h1 := hy _ hu'
      calc u * (x * y * x⁻¹) = x * ((x⁻¹ * u * x) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
        _ = x * y * x⁻¹ * u := by group
    · intro hy u hu
      have hu' : x * u * x⁻¹ ∈ U' := (Subgroup.mem_normalizer_iff.mp hx u).mp hu
      have h1 := hy _ hu'
      calc u * y = x⁻¹ * ((x * u * x⁻¹) * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * y * x⁻¹) * (x * u * x⁻¹)) * x := by rw [h1]
        _ = y * u := by group
  have hTC : T ⊓ Subgroup.normalizer (U' : Set G) ⊓ Subgroup.centralizer (U' : Set G) =
      T ⊓ Subgroup.centralizer (U' : Set G) := by
    rw [inf_assoc, inf_eq_right.mpr hCN]
  refine ⟨?_, ?_⟩
  · have h1 := A4.isSylowTwoOf_inf_normal hTG hCN hCnorm
    rwa [hTC] at h1
  · have hnorm : fsuM T L ⊓ Subgroup.normalizer (U' : Set G) ≤
        Subgroup.normalizer ((fsuM T L ⊓ Subgroup.centralizer (U' : Set G) : Subgroup G) :
          Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyM, hyC⟩
        exact ⟨(fsuM T L).mul_mem ((fsuM T L).mul_mem hx.1 hyM) ((fsuM T L).inv_mem hx.1),
          (Subgroup.mem_normalizer_iff.mp (hCnorm hx.2) y).mp hyC⟩
      · rintro ⟨hyM, hyC⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hCnorm hx.2) y).mpr hyC⟩
        have := (fsuM T L).mul_mem ((fsuM T L).mul_mem ((fsuM T L).inv_mem hx.1) hyM) hx.1
        simpa [mul_assoc] using this
    have h1 := A4.isSylowTwoOf_inf_normal hTN (inf_le_inf_left _ hCN) hnorm
    have h2 : T ⊓ Subgroup.normalizer (U' : Set G) ⊓ (fsuM T L ⊓ Subgroup.centralizer
        (U' : Set G)) = T ⊓ Subgroup.centralizer (U' : Set G) := by
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans hCN))
          (le_inf (inf_le_left.trans S.T_le_fsuM) inf_le_right)
    rwa [h2] at h1

end Setup

end CFSG.Quasithin.H13.Sec77
