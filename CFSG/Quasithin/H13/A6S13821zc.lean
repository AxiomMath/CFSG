module

public import CFSG.Quasithin.H13.A6S13821z
public import CFSG.Quasithin.H13.A6S13821zb
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5Setup
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.NParamRootFourLift

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.E1.LiftS5

namespace A6L24

theorem pow_eight_of_pow_two_pow {σ : Perm (Fin 5)} {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 8 = 1 := by
  have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf σ ∣ 120 := by
    have h3 := orderOf_dvd_natCard σ
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h3
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have h4 : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
    norm_num at h4
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact (Nat.pow_dvd_pow 2 hj3).trans (by norm_num)

theorem card_eq_four_of_sylow {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 60)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : Nat.card U = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hU.2.1
  have hidx : ¬ 2 ∣ U.index := by
    have h2 : ¬ 2 ∣ U.relIndex ⊤ := hU.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  have hmul := Subgroup.card_mul_index U
  rw [hk, hX] at hmul
  have hpos : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hk6 : k < 6 := by
    by_contra h
    push Not at h
    have h1 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 2 ^ k ≤ 60 := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_right _ hpos
    omega
  rw [hk]
  interval_cases k <;> norm_num at hmul ⊢ <;> omega

variable {G : Type} [Group G] {H K : Subgroup G}

omit [Group G] in
theorem mem_pCore_iff' {G : Type} [Group G] {K : Subgroup G} (k : ↥K) :
    k ∈ CFSG.pCore 2 ↥K ↔ (k : G) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff k).symm

theorem quotConj_mk (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    quotConj K g (QuotientGroup.mk k) = QuotientGroup.mk
      (⟨(g : G) * k * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2⟩ : ↥K) := by
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  exact Subgroup.normalizerMonoidHom_apply_apply_coe K g k

theorem quotPerm_eq_one_iff (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (h : ↥H) :
    quotPerm hHK e h = 1 ↔ ∀ u ∈ K, (h : G) * u * (h : G)⁻¹ * u⁻¹ ∈ pCoreOf 2 K := by
  have key : quotPerm hHK e h = 1 ↔ quotConj K (Subgroup.inclusion hHK h) = 1 := by
    simp only [quotPerm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  rw [key]
  constructor
  · intro h1 u hu
    have h2 := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
      φ (QuotientGroup.mk (⟨u, hu⟩ : ↥K))) h1
    simp only [MulAut.one_apply] at h2
    rw [quotConj_mk, QuotientGroup.eq_iff_div_mem, mem_pCore_iff'] at h2
    simpa [div_eq_mul_inv] using h2
  · intro h1
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.one_apply, quotConj_mk, QuotientGroup.eq_iff_div_mem, mem_pCore_iff']
      simpa [div_eq_mul_inv] using h1 k k.2

theorem quotPerm_eq_one_iff_of_mem (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (h : ↥H) (hk : (h : G) ∈ K) :
    quotPerm hHK e h = 1 ↔ (h : G) ∈ pCoreOf 2 K := by
  rw [quotPerm_of_mem hHK e h hk]
  constructor
  · intro h1
    have h2 : e (QuotientGroup.mk ⟨h, hk⟩) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, mem_pCore_iff'] at h2
    exact h2
  · intro h1
    have h2 : (QuotientGroup.mk ⟨h, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff']
      exact h1
    rw [h2, map_one]
    rfl

theorem exists_lift (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {σ : Perm (Fin 5)}
    (hσ : σ ∈ alternatingGroup (Fin 5)) : ∃ k : ↥H, (k : G) ∈ K ∧ quotPerm hHK e k = σ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
  refine ⟨⟨k, hKH k.2⟩, k.2, ?_⟩
  rw [quotPerm_of_mem hHK e _ k.2]
  have : (QuotientGroup.mk ⟨(k : G), k.2⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = e.symm ⟨σ, hσ⟩ := hk
  rw [this, MulEquiv.apply_symm_apply]

theorem quotPerm_eq_one_of_mem_pCoreOf [Finite G] (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (g : ↥H)
    (hg : (g : G) ∈ pCoreOf 2 H) : quotPerm hHK e g = 1 := by
  have hcomm : ∀ σ ∈ alternatingGroup (Fin 5), quotPerm hHK e g * σ = σ * quotPerm hHK e g := by
    intro σ hσ
    obtain ⟨k, hkK, rfl⟩ := exists_lift hKH hHK e hσ
    have hc : (g : G) * k * (g : G)⁻¹ * (k : G)⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHK g.2) k).mp hkK) (K.inv_mem hkK)
    have hcQ : (g : G) * k * (g : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 H := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H k.2) _).mp
        ((pCoreOf 2 H).inv_mem hg)
      have e' : (g : G) * k * (g : G)⁻¹ * (k : G)⁻¹ = (g : G) * ((k : G) * (g : G)⁻¹ * (k : G)⁻¹) :=
        by group
      rw [e']
      exact (pCoreOf 2 H).mul_mem hg h1
    have hcO : (g : G) * k * (g : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 K :=
      (mem_pCore_iff' ⟨_, hc⟩).mp (E1.ThinA5.mem_pCore_of_mem_pCoreOf hKH ⟨_, hc⟩ hcQ)
    have h2 := (quotPerm_eq_one_iff_of_mem hHK e (g * k * g⁻¹ * k⁻¹) hc).mpr hcO
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 := mul_inv_eq_one.mp h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  obtain ⟨h1, h2, h3⟩ := eq_one_of_comm
  exact h3 _ ⟨hcomm _ (Perm.mem_alternatingGroup.mpr h1),
    hcomm _ (Perm.mem_alternatingGroup.mpr h2)⟩

theorem sign_eq_neg_one (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (t : ↥H)
    (ht : ∀ k ∈ K, ∃ y ∈ K, ((t : G) * k⁻¹) * y * ((t : G) * k⁻¹)⁻¹ * y⁻¹ ∉ pCoreOf 2 K) :
    Perm.sign (quotPerm hHK e t) = -1 := by
  rcases Int.units_eq_one_or (Perm.sign (quotPerm hHK e t)) with h | h
  · exfalso
    obtain ⟨k, hkK, hk⟩ := exists_lift hKH hHK e (Perm.mem_alternatingGroup.mpr h)
    obtain ⟨y, hyK, hy⟩ := ht k hkK
    have h1 : quotPerm hHK e (t * k⁻¹) = 1 := by rw [map_mul, map_inv, hk, mul_inv_cancel]
    exact hy (by simpa using (quotPerm_eq_one_iff hHK e _).mp h1 y hyK)
  · exact h

theorem pow_four_eq_one (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {g : ↥H} {k : ℕ}
    (hg : (g : G) ^ 2 ^ k = 1) : quotPerm hHK e g ^ 4 = 1 := by
  apply pow_four_of_pow_eight
  have h1 : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hg)
  exact pow_eight_of_pow_two_pow (k := k) (by rw [← map_pow, h1, map_one])

theorem exists_p0 [Finite G] (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {T₀ : Subgroup G}
    (hsyl : IsSylowTwoOf T₀ K) :
    ∃ p₀ : Fin 5, (∀ x (hx : x ∈ T₀), IsV4 p₀ (quotPerm hHK e ⟨x, hKH (hsyl.1 hx)⟩)) ∧
      ∀ τ, IsV4 p₀ τ → ∃ x, ∃ hx : x ∈ T₀, quotPerm hHK e ⟨x, hKH (hsyl.1 hx)⟩ = τ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥K with hO
  set j : (↥K ⧸ O) →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom
    with hj
  set f : ↥K →* Perm (Fin 5) := j.comp (QuotientGroup.mk' O) with hf
  have hψf : ∀ x (hx : x ∈ T₀),
      quotPerm hHK e ⟨x, hKH (hsyl.1 hx)⟩ = f ⟨x, hsyl.1 hx⟩ := fun x hx =>
    quotPerm_of_mem hHK e _ (hsyl.1 hx)
  set P := (T₀.subgroupOf K).map f with hP
  have hP4 : Nat.card P = 4 := by
    have hU : IsSylowTwoOf (T₀.subgroupOf K) ⊤ := by
      refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm, ?_⟩
      show ¬ 2 ∣ (T₀.subgroupOf K).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hsyl.2.2
    have hU' := A6S20.isSylowTwoOf_map_top (f := QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective _) hU
    have h60 : Nat.card (↥K ⧸ O) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hinj : Function.Injective j := fun x y hxy =>
      e.injective (Subtype.ext (by simpa [hj] using hxy))
    have hPe : P = ((T₀.subgroupOf K).map (QuotientGroup.mk' O)).map j := by
      rw [hP, hf, Subgroup.map_map]
    rw [hPe, Subgroup.card_map_of_injective hinj, card_eq_four_of_sylow h60 hU']
  have hsign : ∀ σ ∈ P, Perm.sign σ = 1 := by
    rintro _ ⟨y, -, rfl⟩
    exact Perm.mem_alternatingGroup.mp (e _).2
  have hinv : ∀ σ ∈ P, σ * σ = 1 := by
    intro σ hσ
    have h4 : σ ^ 4 = 1 := by
      have h1 := pow_card_eq_one' (G := ↥P) (x := ⟨σ, hσ⟩)
      rw [hP4] at h1
      simpa using congrArg Subtype.val h1
    exact mul_self_of_pow_four σ ⟨hsign σ hσ, h4⟩
  have hcomm : ∀ σ ∈ P, ∀ τ ∈ P, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    rw [mul_eq_one_iff_eq_inv.mp (hinv _ (P.mul_mem hσ hτ)), mul_inv_rev,
      inv_eq_of_mul_eq_one_right (hinv σ hσ), inv_eq_of_mul_eq_one_right (hinv τ hτ)]
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP4
    norm_num at hP4
  obtain ⟨a, haP, ha1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hne
  obtain ⟨b, hbP, hbz⟩ : ∃ b ∈ P, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have h2 : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq]; exact hinv a haP) ha1
    have h3 : Subgroup.zpowers a = P :=
      le_antisymm (Subgroup.zpowers_le.mpr haP) fun x hx => hcon x hx
    rw [h3, hP4] at h2
    norm_num at h2
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ Subgroup.one_mem _)
  have hab : a ≠ b := fun h => hbz (h ▸ Subgroup.mem_zpowers a)
  obtain ⟨p₀, hpa, hpb⟩ := exists_isV4 a ⟨hsign a haP, hinv a haP, ha1⟩ b
    ⟨hsign b hbP, hinv b hbP, hb1, hab, hcomm a haP b hbP⟩
  refine ⟨p₀, fun x hx => ?_, fun τ hτ => ?_⟩
  · have hσP : f ⟨x, hsyl.1 hx⟩ ∈ P := ⟨⟨x, hsyl.1 hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hψf x hx]
    exact isV4_of_comm p₀ a ⟨hpa, ha1⟩ b ⟨hpb, hb1, hab⟩ _
      ⟨hcomm _ hσP a haP, hcomm _ hσP b hbP⟩
  · have hτP : τ ∈ P := by
      rcases mem_of_isV4 p₀ a ⟨hpa, ha1⟩ b ⟨hpb, hb1, hab⟩ τ hτ with h | h | h | h
      · rw [h]; exact P.one_mem
      · rw [h]; exact haP
      · rw [h]; exact hbP
      · rw [h]; exact P.mul_mem haP hbP
    obtain ⟨y, hy, rfl⟩ := hτP
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hψf _ (Subgroup.mem_subgroupOf.mp hy)⟩

theorem quotPerm_conj (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (g x : ↥H)
    (hy : (g : G) * x * (g : G)⁻¹ ∈ H) :
    quotPerm hHK e ⟨_, hy⟩ = quotPerm hHK e g * quotPerm hHK e x * (quotPerm hHK e g)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem fix_iff [Finite G] (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {T₀ : Subgroup G}
    (hsyl : IsSylowTwoOf T₀ K) (hO : pCoreOf 2 K ≤ T₀) {p₀ : Fin 5}
    (hp₀ : ∀ x (hx : x ∈ T₀), IsV4 p₀ (quotPerm hHK e ⟨x, hKH (hsyl.1 hx)⟩))
    (hp₀' : ∀ τ, IsV4 p₀ τ → ∃ x, ∃ hx : x ∈ T₀, quotPerm hHK e ⟨x, hKH (hsyl.1 hx)⟩ = τ)
    (g : ↥H) : quotPerm hHK e g p₀ = p₀ ↔ (g : G) ∈ Subgroup.normalizer (T₀ : Set G) := by
  have key : ∀ g : ↥H, quotPerm hHK e g p₀ = p₀ → ∀ x ∈ T₀, (g : G) * x * (g : G)⁻¹ ∈ T₀ := by
    intro g hg x hx
    have hxK := hsyl.1 hx
    have hyK : (g : G) * x * (g : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK g.2) x).mp hxK
    have h1 := isV4_conj (hp₀ x hx) (quotPerm hHK e g)
    rw [hg, ← quotPerm_conj hHK e g ⟨x, hKH hxK⟩ (hKH hyK)] at h1
    obtain ⟨x', hx', hx'ψ⟩ := hp₀' _ h1
    have h2 : quotPerm hHK e ((⟨x', hKH (hsyl.1 hx')⟩ : ↥H)⁻¹ * ⟨_, hKH hyK⟩) = 1 := by
      rw [map_mul, map_inv, hx'ψ, inv_mul_cancel]
    have h3 := (quotPerm_eq_one_iff_of_mem hHK e _ (K.mul_mem (K.inv_mem (hsyl.1 hx')) hyK)).mp h2
    have h4 : x'⁻¹ * ((g : G) * x * (g : G)⁻¹) ∈ T₀ := hO h3
    have e' : (g : G) * x * (g : G)⁻¹ = x' * (x'⁻¹ * ((g : G) * x * (g : G)⁻¹)) := by group
    rw [e']
    exact T₀.mul_mem hx' h4
  constructor
  · intro hg
    have hg' : quotPerm hHK e g⁻¹ p₀ = p₀ := by
      rw [map_inv, Perm.inv_eq_iff_eq]
      exact hg.symm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have h1 := key g⁻¹ hg' _ hx
    rwa [show ((g⁻¹ : ↥H) : G) * ((g : G) * x * (g : G)⁻¹) * ((g⁻¹ : ↥H) : G)⁻¹ = x by
      push_cast
      group] at h1
  · intro hg
    apply fix_of_normalizes
    intro τ hτ
    obtain ⟨x, hx, rfl⟩ := hp₀' τ hτ
    have hy : (g : G) * x * (g : G)⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h1 := hp₀ _ hy
    rwa [quotPerm_conj hHK e g ⟨x, hKH (hsyl.1 hx)⟩] at h1

end A6L24

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_equiv_alt_of_l24 (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (h : IsPSL 2 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K
  have h1 : IsPSL 2 2 2 (Q ⧸ Subgroup.center Q) :=
    IsPSL.of_mulEquiv (QuotientGroup.congr _ _ e₁.symm (Subgroup.map_center_eq e₁.symm)) h
  obtain ⟨eS⟩ := E1.ThinA5.exists_mulEquiv_alt_of_isPSL h1
  have hperf : commutator Q = ⊤ := by
    have hK' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
    have : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.isPerfect_def.mp this
  have hcard : Nat.card (Q ⧸ Subgroup.center Q) ∣ 60 := by
    rw [Nat.card_congr eS.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes hperf _ rfl
      E1.ThinA5.odd_card_center_quot_pCore fun r _ _ hr2 S' =>
        E1.ThinA5.isCyclic_of_card_dvd_sixty hcard hr2 S'
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    eS⟩

end Setting4

end CFSG.Quasithin.H13.A6
