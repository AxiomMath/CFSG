module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainDefs
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainFone
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotNormal
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotTwo

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private def nmhS7 : Subgroup (Equiv.Perm (Fin 8)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 8)) (0 : Fin 8)

namespace N7MSetup

variable {X : Type} [Group X] [Finite X] (S : N7MSetup X)

private theorem nmh_exists_spMat_of_mem_FKgrp {x : X} (hx : x ∈ S.FKgrp) :
    ∃ (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3), IsSign s ∧ (∏ i, s i = 1) ∧
      S.ρ x = spMat σ s :=
  hx

private noncomputable def permPart (x : S.FKgrp) : Equiv.Perm (Fin 8) :=
  Classical.choose (S.nmh_exists_spMat_of_mem_FKgrp x.2)

private theorem permPart_spec (x : S.FKgrp) :
    ∃ s : Fin 8 → ZMod 3, IsSign s ∧ (∏ i, s i = 1) ∧
      S.ρ (x : X) = spMat (S.permPart x) s := by
  obtain ⟨s, hs, hprod, hA⟩ :=
    Classical.choose_spec (S.nmh_exists_spMat_of_mem_FKgrp x.2)
  exact ⟨s, hs, hprod, hA⟩

private noncomputable def permHomFK : S.FKgrp →* Equiv.Perm (Fin 8) where
  toFun := S.permPart
  map_one' := by
    obtain ⟨s, hs, -, hA⟩ := S.permPart_spec (1 : S.FKgrp)
    have heq : spMat (S.permPart (1 : S.FKgrp)) s =
        spMat (1 : Equiv.Perm (Fin 8)) (fun _ => 1) := by
      rw [← hA]
      change S.ρ (1 : X) = spMat (1 : Equiv.Perm (Fin 8)) (fun _ => 1)
      rw [map_one, spMat_one]
    exact (nm_spMat_inj hs (fun _ => Or.inl rfl) heq).1
  map_mul' := by
    intro x y
    obtain ⟨sx, hsx, -, hAx⟩ := S.permPart_spec x
    obtain ⟨sy, hsy, -, hAy⟩ := S.permPart_spec y
    obtain ⟨sxy, hsxy, -, hAxy⟩ := S.permPart_spec (x * y)
    have hxy : S.ρ (((x * y : S.FKgrp) : X)) =
        S.ρ (x : X) * S.ρ (y : X) := by
      rw [Subgroup.coe_mul, map_mul]
    have hs : IsSign (fun j => sx (S.permPart y j) * sy j) :=
      IsSign.mul (fun j => hsx (S.permPart y j)) hsy
    have heq : spMat (S.permPart (x * y)) sxy =
        spMat (S.permPart x * S.permPart y)
          (fun j => sx (S.permPart y j) * sy j) := by
      rw [← spMat_mul, ← hAxy, hxy, hAx, hAy]
    exact (nm_spMat_inj hsxy hs heq).1

private theorem permHomFK_spec (x : S.FKgrp) :
    ∃ s : Fin 8 → ZMod 3, IsSign s ∧ (∏ i, s i = 1) ∧
      S.ρ (x : X) = spMat (S.permHomFK x) s := by
  simpa [permHomFK] using S.permPart_spec x

private theorem permHomFK_eq_one_iff_mem_Fgrp (x : S.FKgrp) :
    S.permHomFK x = 1 ↔ (x : X) ∈ S.Fgrp := by
  constructor
  · intro h1
    obtain ⟨s, hs, hprod, hA⟩ := S.permHomFK_spec x
    rw [S.mem_Fgrp]
    exact ⟨1, s, hs, ⟨rfl, hprod⟩, by rw [hA, h1]⟩
  · intro hF
    rw [S.mem_Fgrp] at hF
    obtain ⟨σ, t, ht, ⟨hσ, hpt⟩, hAt⟩ := hF
    obtain ⟨s, hs, -, hA⟩ := S.permHomFK_spec x
    have heq : spMat (S.permHomFK x) s = spMat (1 : Equiv.Perm (Fin 8)) t := by
      rw [← hA, hAt, hσ]
    exact (nm_spMat_inj hs ht heq).1

private theorem nmh_mem_FKgrp_of_rho_eq_spMat_one {n : X} {g : Equiv.Perm (Fin 8)}
    (h : S.ρ n = spMat g (fun _ => (1 : ZMod 3))) : n ∈ S.FKgrp := by
  rw [S.mem_FKgrp, h]
  exact ⟨g, fun _ => 1, fun _ => Or.inl rfl, by simp, rfl⟩

private theorem nmh_permHomFK_eq_of_rho_eq_spMat_one {n : X} (hnFK : n ∈ S.FKgrp)
    {g : Equiv.Perm (Fin 8)} (h : S.ρ n = spMat g (fun _ => (1 : ZMod 3))) :
    S.permHomFK ⟨n, hnFK⟩ = g := by
  obtain ⟨s, hs, -, hA⟩ := S.permHomFK_spec ⟨n, hnFK⟩
  have heq : spMat (S.permHomFK ⟨n, hnFK⟩) s = spMat g (fun _ => 1) := by
    rw [← hA, h]
  exact (nm_spMat_inj hs (fun _ => Or.inl rfl) heq).1

private theorem nmh_conj_mem_map {R : Subgroup X}
    (hnorm : ∀ n ∈ S.H1grp, ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    {g : Equiv.Perm (Fin 8)} (hg : g ∈ nmhS7)
    {m : Equiv.Perm (Fin 8)} (hm : m ∈ (R.subgroupOf S.FKgrp).map S.permHomFK) :
    g * m * g⁻¹ ∈ (R.subgroupOf S.FKgrp).map S.permHomFK := by
  obtain ⟨x, hxK, rfl⟩ := Subgroup.mem_map.mp hm
  have hxR : (x : X) ∈ R := Subgroup.mem_subgroupOf.mp hxK
  have hg0 : g 0 = 0 := by
    have h := MulAction.mem_stabilizer_iff.mp (show g ∈ MulAction.stabilizer _ _ from hg)
    simpa using h
  have hmem : spMat g (fun _ => (1 : ZMod 3)) ∈ evenAll0 7 :=
    ⟨g, fun _ => 1, fun _ => Or.inl rfl, ⟨hg0, by simp⟩, rfl⟩
  obtain ⟨n, hnρ⟩ := S.surj_H1 (spMat g (fun _ => 1)) hmem
  have hnH : n ∈ S.H1grp := (S.mem_H1grp n).mpr (by rw [hnρ]; exact hmem)
  have hnFK : n ∈ S.FKgrp := S.nmh_mem_FKgrp_of_rho_eq_spMat_one hnρ
  have hpn : S.permHomFK ⟨n, hnFK⟩ = g :=
    S.nmh_permHomFK_eq_of_rho_eq_spMat_one hnFK hnρ
  have hzR : n * (x : X) * n⁻¹ ∈ R := hnorm n hnH (x : X) hxR
  let z : S.FKgrp := ⟨n, hnFK⟩ * x * ⟨n, hnFK⟩⁻¹
  have hzK : z ∈ R.subgroupOf S.FKgrp := by
    rw [Subgroup.mem_subgroupOf]
    simpa [z] using hzR
  have hz : S.permHomFK z = g * S.permHomFK x * g⁻¹ := by
    simp only [z, map_mul, map_inv, hpn]
  rw [← hz]
  exact Subgroup.mem_map.mpr ⟨z, hzK, rfl⟩

private theorem nmh_stabilizer_le_normalizer_map {R : Subgroup X}
    (hnorm : ∀ n ∈ S.H1grp, ∀ r ∈ R, n * r * n⁻¹ ∈ R) :
    nmhS7 ≤ Subgroup.normalizer ((R.subgroupOf S.FKgrp).map S.permHomFK) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact S.nmh_conj_mem_map hnorm hg
  · intro hm
    have h := S.nmh_conj_mem_map hnorm (nmhS7.inv_mem hg) hm
    rwa [show g⁻¹ * (g * m * g⁻¹) * (g⁻¹)⁻¹ = m by group] at h

end N7MSetup

private theorem nmh_alternatingGroup_le_of_not_le_stabilizer
    {M : Subgroup (Equiv.Perm (Fin 8))}
    (hN : nmhS7 ≤ Subgroup.normalizer (M : Set (Equiv.Perm (Fin 8))))
    (hMP : ¬ M ≤ nmhS7) :
    alternatingGroup (Fin 8) ≤ M := by
  have hcoatom : IsCoatom nmhS7 := by
    have h := Equiv.Perm.isCoatom_stabilizer (α := Fin 8) (s := ({0} : Set (Fin 8)))
      (by simp) (by simp) (by norm_num)
    simpa [nmhS7, MulAction.stabilizer_singleton] using h
  have hlt : nmhS7 < M ⊔ nmhS7 := by
    refine lt_of_le_of_ne le_sup_right (Ne.symm ?_)
    intro hEq
    exact hMP (le_trans le_sup_left (le_of_eq hEq))
  have htop : M ⊔ nmhS7 = ⊤ := hcoatom.lt_iff.mp hlt
  have hNtop : Subgroup.normalizer (M : Set (Equiv.Perm (Fin 8))) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ M ⊔ nmhS7 := by rw [htop]; exact Subgroup.mem_top g
    exact (sup_le Subgroup.le_normalizer hN) hg
  have hnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hne : M ≠ ⊥ := fun hbot => hMP (by rw [hbot]; exact bot_le)
  have hntriv : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hne
  exact @Equiv.Perm.alternatingGroup_le_of_normal (Fin 8) _ _ (by norm_num) M hnormal hntriv

private theorem nmh_perm_eq_bot_of_normal_of_odd
    {M : Subgroup (Equiv.Perm (Fin 8))}
    (hN : nmhS7 ≤ Subgroup.normalizer M) (hodd : Odd (Nat.card M)) : M = ⊥ := by
  by_cases hle : M ≤ nmhS7
  · let T : Finset (Fin 8) := Finset.univ.erase 0
    refine perm_eq_bot_of_normal_of_odd T (by decide) ?_ ?_ ?_
    · intro m hm i hi
      have hi0 : i = 0 := by simpa [T] using hi
      have hm0 : m 0 = 0 := by
        have h := MulAction.mem_stabilizer_iff.mp (show m ∈ MulAction.stabilizer _ _ from hle hm)
        simpa using h
      simpa [hi0] using hm0
    · intro g hg m hm
      have hgP : g ∈ nmhS7 := by
        rw [nmhS7, MulAction.mem_stabilizer_iff]
        simpa using hg 0 (by simp [T])
      exact (Subgroup.mem_normalizer_iff.mp (hN hgP) m).mp hm
    · intro m hm
      have hdvd : orderOf m ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hm
      exact ⟨Nat.card M, hodd, orderOf_dvd_iff_pow_eq_one.mp hdvd⟩
  · have hA8 := nmh_alternatingGroup_le_of_not_le_stabilizer hN hle
    let d : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3
    have hdA : d ∈ alternatingGroup (Fin 8) := by
      change Equiv.swap 0 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 8)
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      decide
    have hdM : d ∈ M := hA8 hdA
    have hd2 : orderOf d = 2 := by
      have hd_sq : d * d = 1 := by decide
      have hd_ne : d ≠ 1 := by decide
      have hdvd : orderOf d ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (n := 2) (by rwa [pow_two])
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd_ne
      · exact h
    have hdvdM : orderOf d ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hdM
    rw [hd2] at hdvdM
    obtain ⟨k, hk⟩ := hdvdM
    obtain ⟨l, hl⟩ := hodd
    omega

private theorem nmh_perm_eq_bot_of_normal_of_two
    {M : Subgroup (Equiv.Perm (Fin 8))}
    (hN : nmhS7 ≤ Subgroup.normalizer M) (hM : IsPGroup 2 M) : M = ⊥ := by
  by_cases hle : M ≤ nmhS7
  · let T : Finset (Fin 8) := Finset.univ.erase 0
    refine perm_eq_bot_of_normal_of_two_power T (by decide) ?_ ?_ ?_
    · intro m hm i hi
      have hi0 : i = 0 := by simpa [T] using hi
      have hm0 : m 0 = 0 := by
        have h := MulAction.mem_stabilizer_iff.mp (show m ∈ MulAction.stabilizer _ _ from hle hm)
        simpa using h
      simpa [hi0] using hm0
    · intro g hg m hm
      have hgP : g ∈ nmhS7 := by
        rw [nmhS7, MulAction.mem_stabilizer_iff]
        simpa using hg 0 (by simp [T])
      exact (Subgroup.mem_normalizer_iff.mp (hN hgP) m).mp hm
    · intro m hm
      obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hM (⟨m, hm⟩ : M)
      exact ⟨k, by simpa using congrArg (fun x : M => (x : Equiv.Perm (Fin 8))) hk⟩
  · have hA8 := nmh_alternatingGroup_le_of_not_le_stabilizer hN hle
    let c : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 0 2
    have hc3 : Equiv.Perm.IsThreeCycle c := by
      rw [show c = Equiv.swap 0 1 * Equiv.swap 0 2 from rfl]
      exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    have hcM : c ∈ M := hA8 hc3.mem_alternatingGroup
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hM (⟨c, hcM⟩ : M)
    have hk' : c ^ 2 ^ k = 1 := by
      simpa using congrArg (fun m : M => (m : Equiv.Perm (Fin 8))) hk
    have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hc3.orderOf] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem nm_le_F_of_odd_normal {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {R : Subgroup X} (hRK : R ≤ S.FKgrp)
    (hnorm : ∀ n ∈ S.H1grp, ∀ r ∈ R, n * r * n⁻¹ ∈ R) (hodd : Odd (S.Fgrp.relIndex R)) :
    R ≤ S.Fgrp := by
  let K : Subgroup S.FKgrp := R.subgroupOf S.FKgrp
  let M : Subgroup (Equiv.Perm (Fin 8)) := K.map S.permHomFK
  have hker : S.permHomFK.ker = S.Fgrp.subgroupOf S.FKgrp := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact S.permHomFK_eq_one_iff_mem_Fgrp x
  have hcard : Nat.card M = S.Fgrp.relIndex R := by
    have h := Subgroup.relIndex_ker K S.permHomFK
    rw [hker, Subgroup.relIndex_subgroupOf hRK] at h
    exact h.symm
  have hMbot : M = ⊥ := by
    refine nmh_perm_eq_bot_of_normal_of_odd (S.nmh_stabilizer_le_normalizer_map hnorm) ?_
    rw [hcard]
    exact hodd
  intro r hr
  have hrK : (⟨r, hRK hr⟩ : S.FKgrp) ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    exact hr
  have hm : S.permHomFK ⟨r, hRK hr⟩ ∈ M := Subgroup.mem_map.mpr ⟨_, hrK, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at hm
  exact (S.permHomFK_eq_one_iff_mem_Fgrp ⟨r, hRK hr⟩).mp hm

theorem nm_le_F_of_normal_two {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {T : Subgroup X} (hTK : T ≤ S.FKgrp)
    (hnorm : ∀ n ∈ S.H1grp, ∀ t ∈ T, n * t * n⁻¹ ∈ T) (hT2 : IsPGroup 2 T) : T ≤ S.Fgrp := by
  let K : Subgroup S.FKgrp := T.subgroupOf S.FKgrp
  let M : Subgroup (Equiv.Perm (Fin 8)) := K.map S.permHomFK
  have hK2 : IsPGroup 2 K := by
    intro x
    obtain ⟨k, hk⟩ := hT2 (⟨(x : S.FKgrp), x.2⟩ : T)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    have hk' : ((⟨(x : S.FKgrp), x.2⟩ : T) : X) ^ 2 ^ k = 1 := by
      have := congrArg (fun t : T => (t : X)) hk
      simpa using this
    have hx : (x : S.FKgrp) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using hk'
    simpa using hx
  have hM2 : IsPGroup 2 M := hK2.map S.permHomFK
  have hMbot : M = ⊥ :=
    nmh_perm_eq_bot_of_normal_of_two (S.nmh_stabilizer_le_normalizer_map hnorm) hM2
  intro t ht
  have htK : (⟨t, hTK ht⟩ : S.FKgrp) ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    exact ht
  have hm : S.permHomFK ⟨t, hTK ht⟩ ∈ M := Subgroup.mem_map.mpr ⟨_, htK, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at hm
  exact (S.permHomFK_eq_one_iff_mem_Fgrp ⟨t, hTK ht⟩).mp hm

end CFSG.StandardType.FrameRoute.FS81

end
