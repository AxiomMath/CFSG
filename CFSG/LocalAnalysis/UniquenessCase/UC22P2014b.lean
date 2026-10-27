module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.Quasithin.Background.C2Coprime
public import CFSG.GroupTheory.ComponentCovering
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p2014b_cj_ne {p : ℕ} (hp : p.Prime) {C : Subgroup G} {x : G} (hx : orderOf x = p)
    (hxC : x ∉ normalizer (C : Set G)) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    C ≠ uc22p20bCj (x ^ i) C := by
  intro h
  apply hxC
  have hcop : i.gcd (orderOf x) = 1 := by
    rw [hx]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hi0 hip))
  have hxi : x ^ i ∈ normalizer (C : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm
  exact (Subgroup.zpowers_le.2 hxi) (mem_zpowers_pow_iff.2 hcop)

theorem uc22p2014b_mem_normalizer_cComp (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H)
    (hCM : ¬ C ≤ D.M) {x : G} (hxH : x ∈ H) (hxM : x ∈ D.M) (hx : orderOf x = p) :
    x ∈ normalizer (C : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hxC
  set R := CFSG.Quasithin.solvRad H with hRdef
  have hRM : R ≤ D.M := uc22p2014a_solvRad_le D hB h1930 hH
  have hHR : H ≤ normalizer (R : Set G) := uc22p2014a_le_normalizer_solvRad H
  have hCH : C ≤ H := CFSG.Quasithin.le_of_mem_cComp hC
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hcomm : ∀ i : ℕ, 0 < i → i < p → ⁅C, uc22p20bCj (x ^ i) C⁆ ≤ R := fun i hi0 hip =>
    uc22p20e_comm_le_solvRad hC (uc22p20b_cj_mem_cComp hC (H.pow_mem hxH i))
      (uc22p2014b_cj_ne hp hx hxC hi0 hip)
  have key : ∀ c ∈ C, ∀ s ∈ D.T ⊓ C, c * s * c⁻¹ ∈ D.M := by
    intro c hc s hs
    set f : ℕ → G := fun i => x ^ i * c * (x ^ i)⁻¹ with hf
    have hfx : ∀ i, x * f i * x⁻¹ = f (i + 1) := fun i => by
      simp only [hf, pow_succ']
      group
    have hfE : ∀ i, 0 < i → i < p → f i ∈ uc22p20eCentMod H C := fun i hi0 hip =>
      ⟨H.mul_mem (H.mul_mem (H.pow_mem hxH i) (hCH hc)) (H.inv_mem (H.pow_mem hxH i)),
        fun a ha => hcomm i hi0 hip (Subgroup.commutator_mem_commutator ha
          (uc22p20b_mem_cj.2 ⟨c, hc, rfl⟩))⟩
    set Dn : ℕ → G := fun n => ((List.range n).map f).prod with hDn
    have hDs : ∀ n, Dn (n + 1) = Dn n * f n := fun n => by
      simp only [hDn, List.range_succ, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hA : ∀ n, Dn (n + 1) = c * (x * Dn n * x⁻¹) := by
      intro n
      induction n with
      | zero => simp [hDs, hDn, hf]
      | succ n ih =>
        rw [hDs (n + 1)]
        conv_lhs => rw [ih]
        conv_rhs => rw [hDs n]
        rw [← hfx n]
        group
    have hB' : ∀ n, n < p → x * Dn n * x⁻¹ ∈ uc22p20eCentMod H C := by
      intro n
      induction n with
      | zero => intro _; simpa [hDn] using (uc22p20eCentMod H C).one_mem
      | succ n ih =>
        intro hn
        have e : x * Dn (n + 1) * x⁻¹ = (x * Dn n * x⁻¹) * f (n + 1) := by
          rw [hDs, ← hfx]
          group
        rw [e]
        exact (uc22p20eCentMod H C).mul_mem (ih (by omega)) (hfE (n + 1) (by omega) hn)
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    set E : G := x * Dn (p - 1) * x⁻¹ with hEdef
    have hE : E ∈ uc22p20eCentMod H C := hB' (p - 1) (by omega)
    have hz : Dn p = c * E := by rw [← hp1, hA]
    have hxz : x * Dn p * x⁻¹ = E * c := by
      have hfp : f (p - 1 + 1) = c := by rw [hp1]; simp [hf, hxp]
      rw [← hp1, hDs, ← hfp, ← hfx]
      simp only [hEdef]
      group
    have hcomm' : ⁅x, Dn p⁆ ∈ R := by
      have e : ⁅x, Dn p⁆ = ⁅c, E⁆⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def, hxz, hz, commutatorElement_def]
        group
      rw [e]
      exact R.inv_mem (hE.2 c hc)
    have hzH : Dn p ∈ H := by rw [hz]; exact H.mul_mem (hCH hc) hE.1
    obtain ⟨r, hr, hzr⟩ := uc22p2014a_exists_mul_mem_centralizer hp
      (uc22p2014a_not_dvd_card_solvRad D hB h1930 hsp hH) hx (hHR hxH) (hHR hzH) hcomm'
    have hzM : Dn p ∈ D.M := by
      have h1 : Dn p * r ∈ D.M := hsp.centralizer_le hx1 hxp hxM hzr
      simpa using D.M.mul_mem h1 (D.M.inv_mem (hRM hr))
    have hsE : E⁻¹ * s * E ∈ D.M := by
      have e : E⁻¹ * s * E = s * ⁅s⁻¹, E⁻¹⁆ := by rw [commutatorElement_def]; group
      rw [e]
      exact D.M.mul_mem (D.sylowM.le hs.1)
        (hRM (((uc22p20eCentMod H C).inv_mem hE).2 s⁻¹ (C.inv_mem hs.2)))
    have e : c * s * c⁻¹ = Dn p * (E⁻¹ * s * E) * (Dn p)⁻¹ := by rw [hz]; group
    rw [e]
    exact D.M.mul_mem (D.M.mul_mem hzM hsE) (D.M.inv_mem hzM)
  have hT2 : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ C) C := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hH.1 le_top
    exact CFSG.ABGLocalTools.isSylowOf_iff.1
      (hTH.inf_of_isSubnormal (CFSG.Quasithin.subnormal_of_mem_cComp hC))
  apply hCM
  rw [← CFSG.Quasithin.conjClosure_eq_of_perfect_of_isSylowTwoOf
    (CFSG.Quasithin.perfect_of_mem_cComp hC) hT2]
  exact CFSG.Quasithin.conjClosure_le key

theorem uc22p2014b_cj_mem_cComp_of_calLOf (D : Data G) {H L K : Subgroup G}
    (hL : L ∈ calLOf D.T D.M H) (hK : K ∈ calC L)
    (hLK : L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) {t : G} (ht : t ∈ D.T)
    (hTH : D.T ≤ H) :
    uc22p20bCj t K ∈ CFSG.Quasithin.cComp H ∧ ¬ uc22p20bCj t K ≤ D.M := by
  have hKH : K ∈ CFSG.Quasithin.cComp H :=
    CFSG.Quasithin.cComp_mem_of_subnormal hL.2 (uc22p20e_cComp_of_calC hK)
  refine ⟨uc22p20b_cj_mem_cComp hKH (hTH ht), fun h => uc22p20i_not_le_M D hL.1 ?_⟩
  have hTM : ∀ u ∈ D.T, uc22p20bCj u K ≤ D.M → K ≤ D.M := fun u hu hu' y hy =>
    by simpa [MulAut.conj_apply, mul_assoc] using D.M.mul_mem (D.M.mul_mem
      (D.M.inv_mem (D.sylowM.le hu)) (hu' (uc22p20b_mem_cj.2 ⟨y, hy, rfl⟩))) (D.sylowM.le hu)
  have hKM : K ≤ D.M := hTM t ht h
  rw [hLK]
  refine iSup_le fun u y hy => ?_
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
  have hu := D.sylowM.le u.2
  simpa [MulAut.conj_apply] using D.M.mul_mem (D.M.mul_mem hu (hKM hw)) (D.M.inv_mem hu)

theorem uc22p2014b_mem_normalizer_calLOf (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {L : Subgroup G} (hL : L ∈ calLOf D.T D.M H) {x : G} (hxH : x ∈ H)
    (hxM : x ∈ D.M) (hx : orderOf x = p) : x ∈ normalizer (L : Set G) := by
  obtain ⟨K, hK, hLK⟩ := hL.1.2.2.2
  have hn : ∀ t : D.T, zpowers x ≤ normalizer (K.map (MulAut.conj (t : G)).toMonoidHom : Set G) :=
    fun t => by
      obtain ⟨h1, h2⟩ := uc22p2014b_cj_mem_cComp_of_calLOf D hL hK hLK t.2 hH.1
      exact zpowers_le.2 (uc22p2014b_mem_normalizer_cComp D hB h1930 hp hsp hH h1 h2 hxH hxM hx)
  have := uc22p20b_le_normalizer_iSup _ _ hn (mem_zpowers x)
  rwa [← hLK] at this

theorem uc22p2014b_cComp_le_opp (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H)
    (hCM : ¬ C ≤ D.M) {x : G} (hxH : x ∈ H) (hxM : x ∈ D.M) (hx : orderOf x = p) :
    C ≤ Opp p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxC := uc22p2014b_mem_normalizer_cComp D hB h1930 hp hsp hH hC hCM hxH hxM hx
  set R := CFSG.Quasithin.solvRad H with hRdef
  have hRM : R ≤ D.M := uc22p2014a_solvRad_le D hB h1930 hH
  have hHR : H ≤ normalizer (R : Set G) := uc22p2014a_le_normalizer_solvRad H
  have hCH : C ≤ H := CFSG.Quasithin.le_of_mem_cComp hC
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hgen : ∀ y ∈ H, orderOf y = p → y ∈ Opp p H := fun y hy hyo =>
    Subgroup.subset_closure ⟨hy, 1, by rw [pow_one, hyo]⟩
  have hHO : H ≤ normalizer (Opp p H : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : H.map (MulAut.conj w).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hw)
    have h := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p w H
    unfold CFSG.RankThree.PartOne.conjBy at h
    rw [h1] at h
    exact h.symm
  by_contra hCO
  have hN : C ⊓ Opp p H ≤ R := by
    refine (CFSG.Quasithin.le_solvRad_of_subnormal_lt hC ?_
      (lt_of_le_of_ne inf_le_left fun h => hCO (h ▸ inf_le_right))).trans
      (CFSG.Quasithin.solvRad_le_solvRad_of_subnormal (CFSG.Quasithin.subnormal_of_mem_cComp hC))
    refine CFSG.Quasithin.A3.subnormal_of_normal inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun c hc => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hc) y
    have h2 := Subgroup.mem_normalizer_iff.1 (hHO (hCH hc)) y
    exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩
  apply hCM
  intro c hc
  have hxc : ⁅x, c⁆ ∈ R := by
    refine hN ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact C.mul_mem ((Subgroup.mem_normalizer_iff.1 hxC c).1 hc) (C.inv_mem hc)
    · have e : ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      refine (Opp p H).mul_mem (hgen x hxH hx) (hgen _ ?_ ?_)
      · exact H.mul_mem (H.mul_mem (hCH hc) (H.inv_mem hxH)) (H.inv_mem (hCH hc))
      · rw [← SemiconjBy.orderOf_eq c (by simp [SemiconjBy, mul_assoc] :
          SemiconjBy c x⁻¹ (c * x⁻¹ * c⁻¹)), orderOf_inv, hx]
  obtain ⟨r, hr, hcr⟩ := uc22p2014a_exists_mul_mem_centralizer hp
    (uc22p2014a_not_dvd_card_solvRad D hB h1930 hsp hH) hx (hHR hxH) (hHR (hCH hc)) hxc
  simpa using D.M.mul_mem (hsp.centralizer_le hx1 hxp hxM hcr) (D.M.inv_mem (hRM hr))

theorem uc22p2014b_calLOf_le_opp (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {L : Subgroup G} (hL : L ∈ calLOf D.T D.M H) {x : G} (hxH : x ∈ H)
    (hxM : x ∈ D.M) (hx : orderOf x = p) : L ≤ Opp p H := by
  obtain ⟨K, hK, hLK⟩ := hL.1.2.2.2
  rw [hLK]
  refine iSup_le fun t => ?_
  obtain ⟨h1, h2⟩ := uc22p2014b_cj_mem_cComp_of_calLOf D hL hK hLK t.2 hH.1
  exact uc22p2014b_cComp_le_opp D hB h1930 hp hsp hH h1 h2 hxH hxM hx

end CFSG.LocalAnalysis.UniquenessCase.UC22
