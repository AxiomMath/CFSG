module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Chain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Push CFSG.Quasithin.F53.Stellmacher Equiv

theorem commutator_eq_top_of_core {Γ : Type} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal]
    (hP : IsPGroup 2 P)
    (hgen : Subgroup.closure {x : Γ | ∃ m : ℕ, Odd m ∧ x ^ m = 1} = ⊤)
    (hcomm : commutator Γ ⊔ P = ⊤) : commutator Γ = ⊤ := by
  have hS : ∀ x : Γ, (∃ m : ℕ, Odd m ∧ x ^ m = 1) → x ∈ commutator Γ := by
    rintro x ⟨m, hm, hxm⟩
    have hx : x ∈ commutator Γ ⊔ P := hcomm ▸ Subgroup.mem_top x
    have hnt : Subgroup.normalizer ((commutator Γ : Subgroup Γ) : Set Γ) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    obtain ⟨d, hd, p, hp, hdp⟩ := mem_sup_of_le_normalizer (N := commutator Γ) (K := P)
      (fun g _ => by rw [hnt]; exact Subgroup.mem_top g) hx
    obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
    have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    set π := QuotientGroup.mk' (commutator Γ) with hπ
    have hd1 : π d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    have hπx : π x = π p := by
      rw [hdp, map_mul, hd1, one_mul]
    have h1 : (π p) ^ m = 1 := by rw [← hπx, ← map_pow, hxm, map_one]
    have h2 : (π p) ^ 2 ^ k = 1 := by rw [← map_pow, hpk, map_one]
    have hc : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.Coprime.symm
      (Nat.coprime_two_left.mpr hm))
    have : orderOf (π p) ∣ 1 := hc.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.dvd_one, orderOf_eq_one_iff] at this
    exact (QuotientGroup.eq_one_iff x).mp (hπx.trans this)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  exact fun x hx => hS x hx

variable {G : Type} [Group G] [Finite G]

private theorem two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => left; rfl
  | succ k ih => rw [pow_succ]; omega

theorem oTwoRes_perfect {X : Subgroup G} {θ : ↥X →* Perm (Fin 5)}
    (hθ : Function.Surjective θ) (hker : θ.ker = (pCoreOf 2 X).subgroupOf X) :
    ⁅oTwoRes X, oTwoRes X⁆ = oTwoRes X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := oTwoRes X with hLdef
  have hLX : L ≤ X := oTwoRes_le X
  let θL : ↥L →* Perm (Fin 5) := θ.comp (Subgroup.inclusion hLX)
  have hθL : ∀ x : ↥L, θL x = θ ⟨x.1, hLX x.2⟩ := fun x => rfl
  have hrange : θL.range = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨hxX, hA⟩ := psi_mem_alt_of_mem_oTwoRes θ x.2
      exact hA
    · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro σ hσ
      have h3 : σ ^ 3 = 1 := by rw [← hσ.orderOf]; exact pow_orderOf_eq_one σ
      obtain ⟨x₀, hx₀⟩ := hθ σ
      have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
      obtain ⟨k, m, hm, hn'⟩ := Nat.exists_eq_two_pow_mul_odd hn
      have hym : (x₀ ^ 2 ^ k) ^ m = 1 := by rw [← pow_mul, ← hn']; exact pow_orderOf_eq_one x₀
      have hyL : ((x₀ ^ 2 ^ k : ↥X) : G) ∈ L := by
        refine Subgroup.subset_closure ⟨(x₀ ^ 2 ^ k).2, m, hm, ?_⟩
        simpa using congrArg Subtype.val hym
      have hpow : σ ^ 2 ^ k = σ ∨ σ ^ 2 ^ k = σ⁻¹ := by
        have e : σ ^ 2 ^ k = σ ^ (2 ^ k % 3) := by
          conv_lhs => rw [← Nat.mod_add_div (2 ^ k) 3, pow_add, pow_mul, h3, one_pow, mul_one]
        rcases two_pow_mod_three k with h | h
        · left; rw [e, h, pow_one]
        · right; rw [e, h]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
      have hyσ : θL ⟨_, hyL⟩ = σ ^ 2 ^ k := by
        rw [hθL]; show θ (x₀ ^ 2 ^ k) = _; rw [map_pow, hx₀]
      rcases hpow with h | h
      · exact ⟨_, h ▸ hyσ⟩
      · refine ⟨⟨_, hyL⟩⁻¹, ?_⟩
        rw [map_inv, hyσ, h, inv_inv]
  have hcommimg : (commutator ↥L).map θL = alternatingGroup (Fin 5) := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top, hrange]
    exact commutator_alternatingGroup_eq_self (by simp)
  have hPpg : IsPGroup 2 θL.ker := by
    intro g
    have hg : θ ⟨g.1.1, hLX g.1.2⟩ = 1 := by
      have := g.2
      rw [MonoidHom.mem_ker, hθL] at this
      exact this
    have hmem : g.1.1 ∈ pCoreOf 2 X := by
      have : (⟨g.1.1, hLX g.1.2⟩ : ↥X) ∈ θ.ker := hg
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup (r := 2) X) ⟨g.1.1, hmem⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hcomm : commutator ↥L ⊔ θL.ker = ⊤ := by
    rw [eq_top_iff]
    intro l _
    have hl : θL l ∈ (commutator ↥L).map θL := by
      rw [hcommimg, ← hrange]; exact ⟨l, rfl⟩
    obtain ⟨d, hd, hdl⟩ := hl
    have e : l = d * (d⁻¹ * l) := by group
    rw [e]
    refine Subgroup.mul_mem_sup hd ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, inv_mul_cancel]
  have hgen : Subgroup.closure {x : ↥L | ∃ m : ℕ, Odd m ∧ x ^ m = 1} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hle : L ≤ (Subgroup.closure {x : ↥L | ∃ m : ℕ, Odd m ∧ x ^ m = 1}).map L.subtype := by
      rw [hLdef]
      refine (Subgroup.closure_le _).mpr fun g hg => ?_
      refine ⟨⟨g, Subgroup.subset_closure hg⟩, Subgroup.subset_closure ?_, rfl⟩
      obtain ⟨m, hm, hgm⟩ := hg.2
      exact ⟨m, hm, Subtype.ext (by simpa using hgm)⟩
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have htop := commutator_eq_top_of_core θL.ker hPpg hgen hcomm
  rw [← Subgroup.map_subtype_commutator, htop, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.Quasithin.Kleidman.F53Hss36
