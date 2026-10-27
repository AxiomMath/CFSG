module

public import CFSG.Quasithin.H13.A6S13821L32HatCaseII

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open Equiv

namespace L32HatStep

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem oTwoUpper_mono_gen {A B : Subgroup G} (h : A ≤ B) : oTwoUpper A ≤ oTwoUpper B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem step21 {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∀ x ∈ S.X13820, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  by_cases hXK : S.X13820 ≤ K
  · exact (caseII_false h139 h37 h38 h1334 hS hhat hH hK hKn hP hXK).elim
  · exact step21_of_not_le hH hK hKn hP hXK

theorem mem_mul_of_sup_eq {H K M : Subgroup G} (hK : H ≤ Subgroup.normalizer (K : Set G))
    (hMH : M ≤ H) (hHKM : H = K ⊔ M) : ∀ h ∈ H, ∃ k ∈ K, ∃ m ∈ M, h = k * m := by
  let D : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ m ∈ M, x = k * m}
      one_mem' := ⟨1, K.one_mem, 1, M.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k1, hk1, m1, hm1, rfl⟩ ⟨k2, hk2, m2, hm2, rfl⟩
        refine ⟨k1 * (m1 * k2 * m1⁻¹), K.mul_mem hk1 ?_, m1 * m2, M.mul_mem hm1 hm2, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hK (hMH hm1)) k2).mp hk2
      inv_mem' := by
        rintro _ ⟨k, hk, m, hm, rfl⟩
        refine ⟨m⁻¹ * k⁻¹ * m, ?_, m⁻¹, M.inv_mem hm, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hK (hMH (M.inv_mem hm))) k⁻¹).mp (K.inv_mem hk)
        simpa using this }
  have hsub : H ≤ D := by
    rw [hHKM]
    exact sup_le (fun k hk => ⟨k, hk, 1, M.one_mem, by simp⟩)
      (fun m hm => ⟨1, K.one_mem, m, hm, by simp⟩)
  intro h hh
  obtain ⟨k, hk, m, hm, rfl⟩ := hsub hh
  exact ⟨k, hk, m, hm, rfl⟩

theorem X_le_solvRad {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) : S.X13820 ≤ solvRad H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ⊔ T ≤ H := hH.1.1
  have hL1' : S.L1 ≤ H := le_sup_left.trans hL1H
  have hTH : T ≤ H := le_sup_right.trans hL1H
  have P := S.plusData_X13820
  have hXH : S.X13820 ≤ H := P.le_L1.trans hL1'
  have hstep := step21 h139 h37 h38 h1334 hS hhat hH hK hKn hP
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  obtain ⟨π, hπ, hker, -⟩ := exists_pi_sl3 hK hKn hTsylH hP'
  have hHN : H ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)
  set N : Subgroup G := centralizerMod (pCoreOf 2 K) H K with hNdef
  have hNH : N ≤ H := centralizerMod_le_left _ _ _
  have hXN : S.X13820 ≤ N := fun x hx =>
    ⟨hXH hx, hHN (hXH hx), fun u hu => hstep x hx u hu⟩
  have hNnorm : H ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_centralizerMod hHN Subgroup.le_normalizer hKn
  have hcentral : ∀ n ∈ N, n ∈ K → n ∈ pCoreOf 2 K := by
    intro n hn hnK
    have hcomm : ∀ u ∈ K, n * u * n⁻¹ * u⁻¹ ∈ pCoreOf 2 K := fun u hu => hn.2.2 u hu
    set kn : ↥K := ⟨n, hnK⟩ with hkn
    have hcen : π kn ∈ Subgroup.center SL3.S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := hπ g
      have h1 : π (kn * u * kn⁻¹ * u⁻¹) = 1 := by
        refine (hker _).mpr ?_
        have e : ((kn * u * kn⁻¹ * u⁻¹ : ↥K) : G) = n * (u : G) * n⁻¹ * (u : G)⁻¹ := by
          simp [kn]
        rw [e]
        exact hcomm u u.2
      have h2 : π kn * π u = π u * π kn := by
        have h3 : π kn * π u * (π kn)⁻¹ * (π u)⁻¹ = 1 := by
          simpa [map_mul, map_inv] using h1
        calc π kn * π u = (π kn * π u * (π kn)⁻¹ * (π u)⁻¹) * (π u * π kn) := by group
          _ = π u * π kn := by rw [h3, one_mul]
      exact h2.symm
    have hkn1 : π kn = 1 := by
      have : π kn ∈ (⊥ : Subgroup SL3.S) := by
        rw [← L32HatSL3.center_S_eq_bot]
        exact hcen
      exact Subgroup.mem_bot.mp this
    exact (hker kn).mp hkn1
  haveI : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKn
  haveI hLsolv : Group.IsSolvable ↥(S.L1 ⊔ T) := S.isSolvable_L1T h1334 hS
  have hQsolv : Group.IsSolvable (↥H ⧸ K.subgroupOf H) := by
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (K.subgroupOf H)).comp
      (Subgroup.inclusion hL1H)) ?_
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf H) q
    obtain ⟨k, hk, m, hm, hhkm⟩ := mem_mul_of_sup_eq hKn hL1H hHK (h : G) h.2
    refine ⟨⟨m, hm⟩, ?_⟩
    show QuotientGroup.mk' (K.subgroupOf H) (Subgroup.inclusion hL1H ⟨m, hm⟩) =
      QuotientGroup.mk' (K.subgroupOf H) h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    show (m : G)⁻¹ * (h : G) ∈ K
    rw [hhkm]
    have e2 : (m : G)⁻¹ * (k * m) = m⁻¹ * k * m⁻¹⁻¹ := by group
    rw [e2]
    exact (Subgroup.mem_normalizer_iff.mp (hKn (hL1H (Subgroup.inv_mem _ hm))) k).mp hk
  have hAs : Group.IsSolvable ↥((pCoreOf 2 K).subgroupOf N) := by
    have hAp : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf N) := by
      intro a
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨((a : ↥N) : G), Subgroup.mem_subgroupOf.mp a.2⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    haveI : Group.IsNilpotent ↥((pCoreOf 2 K).subgroupOf N) := IsPGroup.isNilpotent hAp
    infer_instance
  have hNsolv : Group.IsSolvable ↥N := by
    haveI := hAs
    haveI := hQsolv
    refine Group.isSolvable_of_ker_le_range ((pCoreOf 2 K).subgroupOf N).subtype
      ((QuotientGroup.mk' (K.subgroupOf H)).comp (Subgroup.inclusion hNH)) ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxK : (x : G) ∈ K := by
      have h1 : (QuotientGroup.mk' (K.subgroupOf H)) (Subgroup.inclusion hNH x) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hxO : (x : G) ∈ pCoreOf 2 K := hcentral x x.2 hxK
    rw [MonoidHom.mem_range]
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr hxO⟩, rfl⟩
  have hNsr : N ≤ solvRad H :=
    le_sSup ⟨hNH, Subgroup.normal_subgroupOf_of_le_normalizer hNnorm, hNsolv⟩
  exact hXN.trans hNsr

theorem oTwoRes_solvRad_ne_bot_hat {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) : oTwoRes (solvRad H) ≠ ⊥ := by
  have hX := X_le_solvRad h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK
  have hτC : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ∈ S14.C3 := by decide
  have hτ1 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ≠ 1 := by decide
  have P := S.plusData_X13820
  have hXne : S.X13820 ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, hρ⟩ := P.three _ hτC
    rw [hbot, Subgroup.mem_bot] at hx
    have hx1 : x = 1 := Subtype.ext (by simpa using hx)
    rw [hx1, map_one] at hρ
    exact hτ1 hρ.symm
  intro hbot
  apply hXne
  rw [eq_bot_iff]
  calc S.X13820 = oTwoUpper S.X13820 := P.eq
    _ ≤ oTwoUpper (solvRad H) := oTwoUpper_mono_gen hX
    _ = oTwoRes (solvRad H) := (oTwoRes_eq_oTwoUpper _).symm
    _ = ⊥ := hbot

end L32HatStep

end CFSG.Quasithin.H13.A6
