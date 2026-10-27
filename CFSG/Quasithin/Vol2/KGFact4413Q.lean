module

public import CFSG.Quasithin.Vol2.KGFact4413K

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def CoverWeyl (Y : Type) [Group Y] (U A₀ : Subgroup Y) (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (φ : X →* Y), Function.Surjective φ →
    φ.ker ≤ Subgroup.center X → Odd (Nat.card φ.ker) → commutator X = ⊤ →
    ∀ S' D' A' : Subgroup X, IsSylowTwoOf S' ⊤ → D' ≤ Subgroup.normalizer (S' : Set X) →
      Subgroup.normalizer (S' : Set X) ≤ D' ⊔ S' → D' ⊓ S' = ⊥ →
      (∀ a ∈ D', ∀ b ∈ D', a * b = b * a) → A' ≤ D' → (∀ a ∈ A', a ^ p = 1) →
      S'.map φ = U → A'.map φ = A₀ →
      ∃ x : X, x ∉ Subgroup.normalizer (S' : Set X) ∧ x ∈ Subgroup.normalizer (A' : Set X)

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_conj_mem_of_quot {X' : Type} [Group X'] {K : Subgroup Γ} (hKperf : ⁅K, K⁆ = K)
    (ρ : ↥K →* X') (hρ : Function.Surjective ρ) (hO : CFSG.pCore 2 ↥K ≤ ρ.ker)
    (hZ : ∀ k ∈ ρ.ker, ∀ x : ↥K, k * x * k⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥K)
    {S D A : Subgroup Γ} (hS : IsSylowTwoOf S K) (hDK : D ≤ K)
    (hDN : D ≤ Subgroup.normalizer (S : Set Γ))
    (hND : K ⊓ Subgroup.normalizer (S : Set Γ) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {p : ℕ} (hAD : A ≤ D) (hA : ∀ a ∈ A, a ^ p = 1)
    (hX : CoverWeyl X' ((S.subgroupOf K).map ρ) ((A.subgroupOf K).map ρ) p) :
    ∃ x ∈ K, x ∉ Subgroup.normalizer (S : Set Γ) ∧ ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ pCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup K := CFSG.pCore 2 ↥K with hOdef
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  set π : ↥K →* ↥K ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hπk : π.ker = O := QuotientGroup.ker_mk' O
  set φ : ↥K ⧸ O →* X' := QuotientGroup.lift O ρ hO with hφ
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨k, rfl⟩ := hρ x
    exact ⟨π k, rfl⟩
  have hφker : φ.ker ≤ Subgroup.center (↥K ⧸ O) := by
    intro q hq
    obtain ⟨k, rfl⟩ := hπs q
    have hk : k ∈ ρ.ker := hq
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨x, rfl⟩ := hπs q'
    have h1 := hZ k hk x
    have h2 : π (k * x * k⁻¹ * x⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact h1
    have h3 : π k * π x = π x * π k := by
      simp only [map_mul, map_inv] at h2
      calc π k * π x = (π k * π x * (π k)⁻¹ * (π x)⁻¹) * (π x * π k) := by group
        _ = π x * π k := by rw [h2, one_mul]
    exact h3.symm
  have hφodd : Odd (Nat.card φ.ker) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hz1 : (z : ↥K ⧸ O) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hzc : (z : ↥K ⧸ O) ∈ Subgroup.center (↥K ⧸ O) := hφker z.2
    have hzp : IsPGroup 2 (Subgroup.zpowers (z : ↥K ⧸ O)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
    have hzn : (Subgroup.zpowers (z : ↥K ⧸ O)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxc : x ∈ Subgroup.center (↥K ⧸ O) :=
        (Subgroup.zpowers_le.mpr hzc) hx
      rw [Subgroup.mem_center_iff] at hxc
      rw [hxc g, mul_inv_cancel_right]
      exact hx
    have hle : Subgroup.zpowers (z : ↥K ⧸ O) ≤ CFSG.pCore 2 (↥K ⧸ O) := by
      exact CFSG.LieType.BorelTits.le_pCore 2 hzn hzp
    rw [pCore_two_quotient_pCore_two] at hle
    exact hz1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _)))
  have hperf : commutator (↥K ⧸ O) = ⊤ := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hKperf
    exact Group.isPerfect_def.1 inferInstance
  set S' : Subgroup K := S.subgroupOf K with hS'
  have hOS : O ≤ S' := by
    have := hO2.le_sylow_of_normal (A4.toSylow hS)
    rwa [A4.toSylow_coe] at this
  set Sh : Subgroup (↥K ⧸ O) := S'.map π with hSh
  have hcomap : Sh.comap π = S' := by
    rw [hSh, Subgroup.comap_map_eq, hπk, sup_eq_left.mpr hOS]
  have hShSyl : IsSylowTwoOf Sh ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h2 : IsPGroup 2 S' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
      exact h2.map π
    · intro hdvd
      change 2 ∣ Sh.relIndex ⊤ at hdvd
      rw [Subgroup.relIndex_top_right] at hdvd
      exact hS.2.2 (hdvd.trans (Subgroup.index_map_dvd S' hπs))
  have hnorm : ∀ k : ↥K, π k ∈ Subgroup.normalizer (Sh : Set (↥K ⧸ O)) ↔
      (k : Γ) ∈ Subgroup.normalizer (S : Set Γ) := by
    intro k
    rw [← E2.BorelLift.mem_normalizer_subgroupOf_iff hS.1, ← hS', ← hcomap,
      ← Subgroup.comap_normalizer_eq_of_surjective Sh hπs]
    rfl
  set Dh : Subgroup (↥K ⧸ O) := (D.subgroupOf K).map π with hDh
  set Ah : Subgroup (↥K ⧸ O) := (A.subgroupOf K).map π with hAh
  have hDhN : Dh ≤ Subgroup.normalizer (Sh : Set (↥K ⧸ O)) := by
    rintro _ ⟨d, hd, rfl⟩
    exact (hnorm d).mpr (hDN hd)
  have hNDh : Subgroup.normalizer (Sh : Set (↥K ⧸ O)) ≤ Dh ⊔ Sh := by
    intro y hy
    obtain ⟨k, rfl⟩ := hπs y
    have hk : (k : Γ) ∈ K ⊓ Subgroup.normalizer (S : Set Γ) := ⟨k.2, (hnorm k).mp hy⟩
    have hk' : (k : Γ) ∈ ((D ⊔ S : Subgroup Γ) : Set Γ) := hND hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D S hDN] at hk'
    obtain ⟨d, hd, s, hs, hds⟩ := hk'
    have hke : k = ⟨d, hDK hd⟩ * ⟨s, hS.1 hs⟩ := Subtype.ext hds.symm
    rw [hke, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, hd, rfl⟩)
      (Subgroup.mem_sup_right ⟨_, hs, rfl⟩)
  have hDhSh : Dh ⊓ Sh = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨d, hd, rfl⟩, hyS⟩
    have hdo : Odd (orderOf (d : Γ)) := odd_orderOf_of_complement_in hS hDK hDN hDS hd
    have ho : Odd (orderOf (π d)) := by
      rw [Subgroup.orderOf_coe] at hdo
      exact hdo.of_dvd_nat (orderOf_map_dvd π d)
    obtain ⟨m, hm⟩ := hShSyl.2.1 ⟨_, hyS⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_pow_two_pow ho (congrArg Subtype.val hm))
  have hDhab : ∀ a ∈ Dh, ∀ b ∈ Dh, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hDab a ha b hb)
  have hAhD : Ah ≤ Dh := Subgroup.map_mono fun x hx => hAD hx
  have hAhp : ∀ a ∈ Ah, a ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have : a ^ p = 1 := Subtype.ext (by simpa using hA a ha)
    rw [← map_pow, this, map_one]
  have hcomp : φ.comp π = ρ := by
    ext k
    rfl
  have hSφ : Sh.map φ = S'.map ρ := by
    rw [hSh, Subgroup.map_map, hcomp]
  have hAφ : Ah.map φ = (A.subgroupOf K).map ρ := by
    rw [hAh, Subgroup.map_map, hcomp]
  obtain ⟨xh, hxS, hxA⟩ := hX (↥K ⧸ O) φ hφs hφker hφodd hperf Sh Dh Ah hShSyl hDhN hNDh hDhSh
    hDhab hAhD hAhp hSφ hAφ
  obtain ⟨k, rfl⟩ := hπs xh
  refine ⟨k, k.2, fun h => hxS ((hnorm k).mpr h), fun a ha => ?_⟩
  have haK : a ∈ K := hDK (hAD ha)
  have h1 : π k * π ⟨a, haK⟩ * (π k)⁻¹ ∈ Ah :=
    (Subgroup.mem_normalizer_iff.mp hxA _).mp ⟨⟨a, haK⟩, ha, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  have h2 : k * ⟨a, haK⟩ * k⁻¹ ∈ A.subgroupOf K ⊔ O := by
    rw [← hπk, ← Subgroup.comap_map_eq]
    exact h1
  have hpc : pCoreOf 2 K = O.map K.subtype := by
    rw [hOdef]
    rfl
  have h3 := Subgroup.mem_map_of_mem K.subtype h2
  rw [Subgroup.map_sup, ← hpc, Subgroup.subgroupOf_map_subtype] at h3
  have h4 : A ⊓ K ⊔ pCoreOf 2 K ≤ A ⊔ pCoreOf 2 K := sup_le_sup_right inf_le_left _
  exact h4 h3

theorem le_of_case_two {H S MH K B : Subgroup Γ} (hmin : MinParabolic H S MH) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ S) (hTK : S ≤ Subgroup.normalizer (K : Set Γ)) (hBM : B ≤ MH)
    (hBo : Odd (Nat.card B)) : B ≤ K := by
  have hT : IsSylowTwoOf S H := hmin.isSylow
  have hMH : MH ≤ H := hmin.maximal.1.le
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHN : H ≤ Subgroup.normalizer (K : Set Γ) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hKidx : ∃ k : ℕ, K.relIndex H = 2 ^ k := by
    have h1 : K.relIndex (S ⊔ K) = K.relIndex S := A4.relIndex_sup_eq_of_le_normalizer' hTK
    rw [sup_comm, ← hHK] at h1
    obtain ⟨m, hm⟩ := hT.2.1.exists_card_eq
    exact E2.BorelLift.exists_eq_two_pow_of_dvd (h1 ▸ hm ▸ Subgroup.relIndex_dvd_card K S)
  obtain ⟨kk, hkk⟩ := hKidx
  exact E2.BorelLift.le_of_odd hKH hHN hkk (hBM.trans hMH) hBo

theorem not_le_of_case_two_of {H S MH K B A R : Subgroup Γ} {p : ℕ}
    (hmin : MinParabolic H S MH) (hK : K ∈ cComp H) (hHK : H = K ⊔ S)
    (hTK : S ≤ Subgroup.normalizer (K : Set Γ))
    (hJ : ∀ x : Γ, x ∈ kerIn MH H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star MH H K) (E2.star MH H (MH ⊓ K))) (hRS : R ≤ S)
    (hMR : MH ≤ Subgroup.normalizer (R : Set Γ)) (hBM : B ≤ MH) (hBo : Odd (Nat.card B))
    (hBR : MH ⊓ oTwoUpper H ≤ B ⊔ R) (hBab : IsMulCommutative ↥B) (hAB : A ≤ B)
    (hA : ∀ a ∈ A, a ^ p = 1)
    (hX : CoverWeyl ↥(E2.star MH H K)
      (((S ⊓ K).subgroupOf K).map (starRes MH H K (le_of_mem_cComp hK)))
      ((A.subgroupOf K).map (starRes MH H K (le_of_mem_cComp hK))) p) :
    ¬ H ⊓ Subgroup.normalizer (A : Set Γ) ≤ MH := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf S H := hmin.isSylow
  have hTM : S ≤ MH := hmin.le
  have hMH : MH ≤ H := hmin.maximal.1.le
  set Q : Subgroup Γ := pCoreOf 2 H with hQ
  have hQT : Q ≤ S := E2.BorelLift.pCoreOf_le_of_sylow hT
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hsK : IsSylowTwoOf (S ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hT
  have hcommJ : ∀ j ∈ K, j ∈ kerIn MH H → ∀ x ∈ K, j * x * j⁻¹ * x⁻¹ ∈ K ⊓ Q := by
    intro j hjK hjJ x hxK
    exact ⟨K.mul_mem (K.mul_mem (K.mul_mem hjK hxK) (K.inv_mem hjK)) (K.inv_mem hxK),
      ((hJ j).mp hjJ).2 x (Subgroup.mem_sup_left hxK)⟩
  have hJK : ∀ j ∈ K, j ∈ kerIn MH H → ∀ x ∈ S ⊓ K, j * x * j⁻¹ ∈ S ⊓ K := by
    intro j hjK hjJ x hx
    have h1 := hcommJ j hjK hjJ x hx.2
    have h2 : j * x * j⁻¹ * x⁻¹ ∈ S ⊓ K := ⟨hQT h1.2, h1.1⟩
    have := (S ⊓ K).mul_mem h2 hx
    simpa using this
  have hBeq : MH ⊓ K = K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup Γ) : Set Γ) :=
    E2.BorelLift.inf_eq_normalizer hT hTM hK hB hJK
  have hBK : B ≤ K := le_of_case_two hmin hK hHK hTK hBM hBo
  have hKO : K ≤ oTwoUpper H := by
    rw [Vol2.Ch11.SecB.oTwoUpper_eq_conjClosure hperf hT.2.1 hHK]
    exact le_conjClosure K H
  have hBN : B ≤ Subgroup.normalizer ((S ⊓ K : Subgroup Γ) : Set Γ) := by
    intro b hb
    have : b ∈ MH ⊓ K := ⟨hBM hb, hBK hb⟩
    rw [hBeq] at this
    exact this.2
  have hND : K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup Γ) : Set Γ) ≤ B ⊔ (S ⊓ K) := by
    intro m hm
    rw [← hBeq] at hm
    have hm' : m ∈ ((B ⊔ R : Subgroup Γ) : Set Γ) := hBR ⟨hm.1, hKO hm.2⟩
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B R (hBM.trans hMR)] at hm'
    obtain ⟨b, hb, r, hr, rfl⟩ := hm'
    have hrK : r ∈ K := by
      have := K.mul_mem (K.inv_mem (hBK hb)) hm.2
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right ⟨hRS hr, hrK⟩)
  have hBS : B ⊓ (S ⊓ K) = ⊥ := E2.BorelLift.inf_eq_bot_of_odd hBo (hT.2.1.to_le inf_le_left)
  have hBab' : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hO : CFSG.pCore 2 ↥K ≤ (starRes MH H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starRes_eq_one_iff]
    have h1 : (k : Γ) ∈ pCoreOf 2 K := E2.BorelLift.coe_mem_pCoreOf hk
    exact E2.BorelLift.pCoreOf_le_kerIn hT hTM
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) h1)
  have hZ : ∀ k ∈ (starRes MH H K hKH).ker, ∀ x : ↥K,
      k * x * k⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥K := by
    intro k hk x
    rw [MonoidHom.mem_ker, starRes_eq_one_iff] at hk
    apply E2.BorelLift.mem_pCore_of_coe
    have h1 := hcommJ k k.2 hk x x.2
    exact Vol2.Ch11.SecB.inf_pCoreOf_le_pCoreOf hKH h1
  obtain ⟨x, hxK, hxN, hxA⟩ := exists_conj_mem_of_quot hperf (starRes MH H K hKH)
    (starRes_surjective hKH) hO hZ hsK hBK hBN hND hBS hBab' hAB hA hX
  have hxM : x ∉ MH := by
    intro hxM
    have : x ∈ MH ⊓ K := ⟨hxM, hxK⟩
    rw [hBeq] at this
    exact hxN this.2
  have hP₂T : pCoreOf 2 K ≤ S :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans hQT
  refine not_le_of_conj_mem_sup (hKH hxK) hxM (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    (hP₂T.trans hTM) hMH ?_ (hBo.of_dvd_nat (Subgroup.card_dvd_of_le hAB)) hxA
  exact (hAB.trans hBK).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)

end CFSG.Quasithin.H13.KG4413
