module

public import CFSG.Quasithin.Vol2.Ch11SecGTBar
public import CFSG.Quasithin.Vol2.Ch11SecGTSL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG.Bar

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] noncomputable def rhoL {K L₁ : Subgroup G} (hL : L₁ ≤ K) : ↥L₁ →* KBar K :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hL)

theorem rhoL_apply {K L₁ : Subgroup G} (hL : L₁ ≤ K) (l : ↥L₁) :
    rhoL hL l = ((⟨(l : G), hL l.2⟩ : ↥K) : KBar K) := rfl

theorem ker_rhoL_le {K L₁ : Subgroup G} (hL : L₁ ≤ K) : (rhoL hL).ker ≤ CFSG.pCore 2 ↥L₁ := by
  refine le_sSup ⟨MonoidHom.normal_ker _, fun x => ?_⟩
  have hx : Subgroup.inclusion hL (x : ↥L₁) ∈ CFSG.pCore 2 ↥K := by
    have h := (MonoidHom.mem_ker).mp x.2
    change ((Subgroup.inclusion hL (x : ↥L₁) : ↥K) : KBar K) = 1 at h
    rwa [QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hx⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => ((y : ↥K) : G)) hk
  simpa using this

theorem eq_bot_of_odd_of_le_range {K L₁ : Subgroup G} (hL : L₁ ≤ K) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 4) (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* SL(2, F))
    {M : Subgroup (KBar K)} (hMr : M ≤ (rhoL hL).range)
    (hMn : ∀ l : ↥L₁, ∀ m ∈ M, rhoL hL l * m * (rhoL hL l)⁻¹ ∈ M)
    (hodd : ∀ m ∈ M, ∃ n : ℕ, Odd n ∧ m ^ n = 1) : M = ⊥ := by
  set P₁ := CFSG.pCore 2 ↥L₁
  set M' := M.comap (rhoL hL) with hM'
  have hM'n : M'.Normal := ⟨fun l hl g => by
    rw [hM', Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hMn g _ hl⟩
  set N'' := (M'.map (QuotientGroup.mk' P₁)).map e.toMonoidHom with hN''
  have hN''n : N''.Normal :=
    (hM'n.map _ (QuotientGroup.mk'_surjective P₁)).map _ e.surjective
  have hM'P : ∀ l ∈ M', ∃ n : ℕ, Odd n ∧ l ^ n ∈ P₁ := by
    intro l hl
    obtain ⟨n, hn, hln⟩ := hodd _ hl
    refine ⟨n, hn, ker_rhoL_le hL ?_⟩
    rw [MonoidHom.mem_ker, map_pow, hln]
  have hbot : N'' = ⊥ := by
    refine SL2.eq_bot_of_normal_of_odd (by omega) N'' hN''n ?_
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    obtain ⟨n, hn, hlnP⟩ := hM'P l hl
    refine ⟨n, hn, ?_⟩
    rw [← map_pow, ← map_pow, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hlnP,
      map_one]
  have hM'P₁ : ∀ l ∈ M', l ∈ P₁ := by
    intro l hl
    have h1 : e.toMonoidHom (QuotientGroup.mk' P₁ l) ∈ N'' :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hl)
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : QuotientGroup.mk' P₁ l = 1 := e.injective (by simpa using h1)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨l, rfl⟩ := hMr hm
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup ⟨l, hM'P₁ l hm⟩
  obtain ⟨n, hn, hmn⟩ := hodd _ hm
  have h1 : rhoL hL l ^ 2 ^ j ∈ (⊥ : Subgroup (KBar K)) := by
    rw [Subgroup.mem_bot, ← map_pow]
    have : l ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this, map_one]
  have h2 : rhoL hL l ^ n ∈ (⊥ : Subgroup (KBar K)) := by
    rw [Subgroup.mem_bot]
    exact hmn
  have h3 := pow_gcd_mem h1 h2
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hn)),
    pow_one] at h3

theorem mem_range_of_mem_cBar {K L₁ Y : Subgroup G} (hL : L₁ ≤ K)
    (hCL : K ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (L₁ : Set G))
    {c : KBar K} (hc : c ∈ cBar K Y) (l : ↥L₁) : c * rhoL hL l * c⁻¹ ∈ (rhoL hL).range := by
  obtain ⟨c, hc, rfl⟩ := hc
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hc
  have hcl' : (c : G) * l * (c : G)⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp (hCL hc) l).mp l.2
  refine ⟨⟨_, hcl'⟩, ?_⟩
  rw [rhoL_apply, rhoL_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem le_center_of_odd {K L₁ Y : Subgroup G} (hL : L₁ ≤ K)
    (hcl : CFSG.Quasithin.conjClosure L₁ K = K) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* SL(2, F))
    (hCL : K ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (L₁ : Set G))
    {N : Subgroup (KBar K)} [hN : N.Normal] (hNC : N ≤ cBar K Y)
    (hodd : ∀ n ∈ N, ∃ m : ℕ, Odd m ∧ n ^ m = 1) : N ≤ Subgroup.center (KBar K) := by
  set M := N ⊓ (rhoL hL).range with hM
  have hMbot : M = ⊥ := by
    refine eq_bot_of_odd_of_le_range hL hF e inf_le_right ?_ ?_
    · intro l m hm
      exact ⟨hN.conj_mem _ hm.1 _, (rhoL hL).range.mul_mem
        ((rhoL hL).range.mul_mem ⟨l, rfl⟩ hm.2) ((rhoL hL).range.inv_mem ⟨l, rfl⟩)⟩
    · intro m hm
      exact hodd m hm.1
  refine le_center_of_commute hL hcl (fun n hn l hl => ?_)
  show n * rhoL hL ⟨l, hl⟩ = rhoL hL ⟨l, hl⟩ * n
  have hc : n * rhoL hL ⟨l, hl⟩ * n⁻¹ * (rhoL hL ⟨l, hl⟩)⁻¹ ∈ M := by
    refine ⟨?_, ?_⟩
    · have : n * (rhoL hL ⟨l, hl⟩ * n⁻¹ * (rhoL hL ⟨l, hl⟩)⁻¹) ∈ N :=
        mul_mem hn (hN.conj_mem _ (inv_mem hn) _)
      simpa [mul_assoc] using this
    · exact (rhoL hL).range.mul_mem (mem_range_of_mem_cBar hL hCL (hNC hn) ⟨l, hl⟩)
        ((rhoL hL).range.inv_mem ⟨⟨l, hl⟩, rfl⟩)
  rw [hMbot, Subgroup.mem_bot] at hc
  calc n * rhoL hL ⟨l, hl⟩ =
        (n * rhoL hL ⟨l, hl⟩ * n⁻¹ * (rhoL hL ⟨l, hl⟩)⁻¹) * (rhoL hL ⟨l, hl⟩ * n) := by group
    _ = rhoL hL ⟨l, hl⟩ * n := by rw [hc, one_mul]

end CFSG.Quasithin.Vol2.Ch11.SecG.Bar
