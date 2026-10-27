module

public import CFSG.RankThree.PartTwo.Sec18.Item187NFixOrder
public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

theorem le_finrank_of_cyclic_faithful {F : Type*} [Group F] [IsCyclic F] [Finite F]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) F V) (hfaith : Function.Injective ρ) :
    (Nat.card F = 13 → 12 ≤ Module.finrank (ZMod 2) V) ∧
      (∀ m : ℕ, Odd m → 3 ≤ m → Nat.card F = 4 ^ m + 2 ^ m + 1 →
        9 ≤ Module.finrank (ZMod 2) V) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F)
  have hord : orderOf g = Nat.card F := orderOf_eq_card_of_forall_mem_zpowers hg
  have hρord : orderOf (ρ g) = Nat.card F := by rw [orderOf_injective ρ hfaith g, hord]
  have key : ∀ N : ℕ, Nat.card F = N → Odd N →
      N ∣ lcmPowTwoSubOne (Module.finrank (ZMod 2) V) := by
    intro N hN hodd
    have h1 : ρ g ^ N = 1 := by rw [← hN, ← hρord]; exact pow_orderOf_eq_one _
    have h2 := pow_lcmPowTwoSubOne_eq_one (ρ g) hodd h1
    rw [← hN, ← hρord]
    exact orderOf_dvd_of_pow_eq_one h2
  constructor
  · intro h13
    by_contra hlt
    push Not at hlt
    have hd := key 13 h13 (by decide)
    exact not_thirteen_dvd_lcmPowTwoSubOne (hd.trans (lcmPowTwoSubOne_mono (by omega)))
  · intro m hm h3 hN
    by_contra hlt
    push Not at hlt
    have hodd : Odd (4 ^ m + 2 ^ m + 1) := by
      have h4 : Even (4 ^ m) := Nat.even_pow.mpr ⟨by decide, by omega⟩
      have h2 : Even (2 ^ m) := Nat.even_pow.mpr ⟨by decide, by omega⟩
      exact (h4.add h2).add_one
    have hd := key _ hN hodd
    exact not_dvd_lcmPowTwoSubOne_eight hm h3 (hd.trans (lcmPowTwoSubOne_mono (by omega)))

section FixDimHelpers

variable {H : Type*} [Group H]

private theorem sum_left_mul_eq {M : Type*} [AddCommMonoid M] (F : Subgroup H) [Fintype F]
    {g : H} (hg : g ∈ F) (φ : H → M) :
    ∑ f : F, φ (g * f) = ∑ f : F, φ f :=
  Fintype.sum_bijective (fun f : F => (⟨g, hg⟩ : F) * f)
    (Finite.injective_iff_bijective.mp (mul_right_injective (⟨g, hg⟩ : F))) _ _ (fun _ => rfl)

private theorem sum_conj_eq {M : Type*} [AddCommMonoid M] (F : Subgroup H) [Fintype F]
    {g : H} (hg : ∀ f ∈ F, g * f * g⁻¹ ∈ F) (φ : H → M) :
    ∑ f : F, φ (g * f * g⁻¹) = ∑ f : F, φ f := by
  have hinj : Function.Injective (fun f : F => (⟨g * f * g⁻¹, hg f f.2⟩ : F)) := by
    intro a b hab
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  exact Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp hinj) _ _ (fun _ => rfl)

private theorem nsmul_eq_self_of_odd {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ}
    (hn : Odd n) (x : M) : n • x = x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_eq_one_iff_odd.mpr hn, one_smul]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def fixProj (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] : Module.End (ZMod 2) V :=
  ∑ f : F, ρ (f : H)

private theorem fixProj_mul_of_mem (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] {g : H} (hg : g ∈ F) : ρ g * fixProj ρ F = fixProj ρ F := by
  show ρ g * ∑ f : F, ρ (f : H) = ∑ f : F, ρ (f : H)
  rw [Finset.mul_sum]
  simp only [← map_mul]
  exact sum_left_mul_eq F hg ⇑ρ

private theorem fixProj_mul_self (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] (hodd : Odd (Nat.card F)) : fixProj ρ F * fixProj ρ F = fixProj ρ F := by
  calc fixProj ρ F * fixProj ρ F = ∑ f : F, ρ (f : H) * fixProj ρ F := by
        show (∑ f : F, ρ (f : H)) * fixProj ρ F = _
        rw [Finset.sum_mul]
    _ = ∑ _f : F, fixProj ρ F := Finset.sum_congr rfl fun f _ => fixProj_mul_of_mem ρ F f.2
    _ = fixProj ρ F := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact nsmul_eq_self_of_odd hodd _

private theorem fixProj_apply_of_fixed (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] (hodd : Odd (Nat.card F)) {v : V} (hv : ∀ f : F, ρ (f : H) v = v) :
    fixProj ρ F v = v := by
  show (∑ f : F, ρ (f : H)) v = v
  rw [LinearMap.sum_apply]
  simp only [hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  exact nsmul_eq_self_of_odd hodd v

private theorem fixProj_apply_mem (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] {f : H} (hf : f ∈ F) (v : V) : ρ f (fixProj ρ F v) = fixProj ρ F v := by
  have h := congrArg (fun T : Module.End (ZMod 2) V => T v) (fixProj_mul_of_mem ρ F hf)
  simpa only [Module.End.mul_apply] using h

private theorem fixProj_mul_comm (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] {g : H} (hg : ∀ f ∈ F, g * f * g⁻¹ ∈ F) :
    fixProj ρ F * ρ g = ρ g * fixProj ρ F := by
  have h1 : ρ g * fixProj ρ F * ρ g⁻¹ = fixProj ρ F := by
    show ρ g * (∑ f : F, ρ (f : H)) * ρ g⁻¹ = ∑ f : F, ρ (f : H)
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [← map_mul]
    exact sum_conj_eq F hg ⇑ρ
  calc fixProj ρ F * ρ g = (ρ g * fixProj ρ F * ρ g⁻¹) * ρ g := by rw [h1]
    _ = ρ g * fixProj ρ F := by
        rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

private theorem fixProj_apply_comm (ρ : Representation (ZMod 2) H V) (F : Subgroup H)
    [Fintype F] {g : H} (hg : ∀ f ∈ F, g * f * g⁻¹ ∈ F) {w : V}
    (hw : fixProj ρ F w = 0) : fixProj ρ F (ρ g w) = 0 := by
  rw [← Module.End.mul_apply, fixProj_mul_comm ρ F hg, Module.End.mul_apply, hw, map_zero]

private noncomputable def restrictRep (ρ : Representation (ZMod 2) H V) (M : Subgroup H)
    (W : Submodule (ZMod 2) V) (hW : ∀ m ∈ M, ∀ w ∈ W, ρ m w ∈ W) :
    Representation (ZMod 2) ↥M ↥W where
  toFun m := (ρ (m : H)).restrict (fun w hw => hW (m : H) m.2 w hw)
  map_one' := by
    ext w
    simp [LinearMap.restrict_apply]
  map_mul' m n := by
    ext w
    simp [LinearMap.restrict_apply]

private theorem commute_of_zpow_ne_one {c x : H} (hc : orderOf c = 3) (n : ℤ) (hn : c ^ n ≠ 1)
    (hx : Commute (c ^ n) x) : Commute c x := by
  have hmod : c ^ (n % 3) = c ^ n := by
    have h := zpow_mod_orderOf c n
    rw [hc] at h
    exact_mod_cast h
  have hc3 : c ^ 3 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · exfalso
    apply hn
    rw [← hmod, h, zpow_zero]
  · rw [← hmod, h, zpow_one] at hx
    exact hx
  · rw [← hmod, h] at hx
    have h2 : c ^ (2 : ℤ) = c ^ 2 := by norm_cast
    rw [h2] at hx
    have hcc : c ^ 2 * c ^ 2 = c := by
      rw [← pow_add]
      calc c ^ (2 + 2) = c ^ 3 * c := by rw [← pow_succ]
        _ = c := by rw [hc3, one_mul]
    rw [← hcc]
    exact hx.mul_left hx

private theorem mem_zpowers_self_gen {G : Type*} [Group G] (g : G) (x : ↥(Subgroup.zpowers g)) :
    x ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

end FixDimHelpers

theorem three_le_finrank_invariants {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (F : Subgroup H) (hFc : IsCyclic F) (c : H)
    (hc : orderOf c = 3) (hcF : c ∈ Subgroup.normalizer (F : Set H))
    (hfpf : ∀ f ∈ F, c * f = f * c → f = 1)
    (hfaith : Function.Injective (ρ.comp F.subtype))
    (hcard : Nat.card F = 13 ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ Nat.card F = 4 ^ m + 2 ^ m + 1) :
    3 ≤ Module.finrank (ZMod 2)
      (Representation.invariants (ρ.comp (Subgroup.zpowers c).subtype)) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := by
    rcases hcard with h | ⟨m, hm, h3, h⟩
    · rw [h]
      decide
    · rw [h]
      have h4 : Even (4 ^ m) := Nat.even_pow.mpr ⟨by decide, by omega⟩
      have h2 : Even (2 ^ m) := Nat.even_pow.mpr ⟨by decide, by omega⟩
      exact (h4.add h2).add_one
  set N : Subgroup H := Subgroup.normalizer (F : Set H)
  have hFN : F ≤ N := Subgroup.le_normalizer
  have hcN : c ∈ N := hcF
  have hgN : ∀ g ∈ N, ∀ f ∈ F, g * f * g⁻¹ ∈ F := fun g hg f hf =>
    (Subgroup.mem_normalizer_iff.mp hg f).mp hf
  have hV'N : ∀ g ∈ N, ∀ w ∈ LinearMap.ker (fixProj ρ F), ρ g w ∈ LinearMap.ker (fixProj ρ F) :=
    fun g hg w hw =>
      LinearMap.mem_ker.mpr (fixProj_apply_comm ρ F (hgN g hg) (LinearMap.mem_ker.mp hw))
  have hV'F : ∀ f ∈ F, ∀ w ∈ LinearMap.ker (fixProj ρ F), ρ f w ∈ LinearMap.ker (fixProj ρ F) :=
    fun f hf => hV'N f (hFN hf)
  have hinjF : Function.Injective (restrictRep ρ F (LinearMap.ker (fixProj ρ F)) hV'F) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply hfaith
    show ρ (a : H) = ρ 1
    rw [map_one]
    ext v
    rw [Module.End.one_apply]
    have hPP : fixProj ρ F (fixProj ρ F v) = fixProj ρ F v := by
      rw [← Module.End.mul_apply, fixProj_mul_self ρ F hodd]
    have hv : v - fixProj ρ F v ∈ LinearMap.ker (fixProj ρ F) := by
      rw [LinearMap.mem_ker, map_sub, hPP, sub_self]
    have h1 : ρ (a : H) (fixProj ρ F v) = fixProj ρ F v := fixProj_apply_mem ρ F a.2 v
    have h2 : ρ (a : H) (v - fixProj ρ F v) = v - fixProj ρ F v :=
      congrArg Subtype.val (LinearMap.congr_fun ha ⟨v - fixProj ρ F v, hv⟩)
    have hsplit : ρ (a : H) v = ρ (a : H) (fixProj ρ F v) + ρ (a : H) (v - fixProj ρ F v) := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, h1, h2]
    abel
  have hdim : 9 ≤ Module.finrank (ZMod 2) (LinearMap.ker (fixProj ρ F)) := by
    rcases hcard with h | ⟨m, hm, h3, h⟩
    · have := (le_finrank_of_cyclic_faithful (restrictRep ρ F (LinearMap.ker (fixProj ρ F)) hV'F)
        hinjF).1 h
      omega
    · have := (le_finrank_of_cyclic_faithful (restrictRep ρ F (LinearMap.ker (fixProj ρ F)) hV'F)
        hinjF).2 m hm h3 h
      omega
  have hfixV' : Representation.invariants
      ((restrictRep ρ N (LinearMap.ker (fixProj ρ F)) hV'N).comp (F.subgroupOf N).subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    rw [Representation.mem_invariants] at hw
    have hfix : ∀ f : F, ρ (f : H) (w : V) = (w : V) := fun f =>
      congrArg Subtype.val (hw ⟨⟨(f : H), hFN f.2⟩, Subgroup.mem_subgroupOf.mpr f.2⟩)
    have hPw : fixProj ρ F (w : V) = (w : V) := fixProj_apply_of_fixed ρ F hodd hfix
    exact Subtype.ext (hPw.symm.trans (LinearMap.mem_ker.mp w.2))
  set c' : N := ⟨c, hcN⟩
  have hKn : (F.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).mpr le_rfl
  have hBK : Subgroup.zpowers c' ≤
      Subgroup.normalizer (((F.subgroupOf N : Subgroup N)) : Set N) := by
    haveI := hKn
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hKc : IsMulCommutative (F.subgroupOf N) := by
    have hFcomm : ∀ a b : F, a * b = b * a := fun a b =>
      (inferInstance : IsMulCommutative F).is_comm.comm a b
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (Subtype.val : F → H)
      (hFcomm ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩ ⟨y.1.1, Subgroup.mem_subgroupOf.mp y.2⟩)
  have hchar : ¬ ringChar (ZMod 2) ∣ Nat.card (F.subgroupOf N) := by
    rw [ZMod.ringChar_zmod_n, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv]
    have h := Nat.odd_iff.mp hodd
    omega
  have hfpf' : ∀ b ∈ Subgroup.zpowers c', b ≠ 1 → ∀ k ∈ F.subgroupOf N,
      b * k = k * b → k = 1 := by
    intro b hb hb1 k hk hbk
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbH : (b : H) = c ^ n := by
      rw [← hn]
      exact SubgroupClass.coe_zpow c' n
    have hne : c ^ n ≠ 1 := by
      rw [← hbH]
      intro h
      exact hb1 (Subtype.ext h)
    have hcomm : Commute (b : H) (k : H) := congrArg Subtype.val hbk
    have hck : Commute c (k : H) := by
      refine commute_of_zpow_ne_one hc n hne ?_
      rw [← hbH]
      exact hcomm
    exact Subtype.ext (hfpf _ (Subgroup.mem_subgroupOf.mp hk) hck.eq)
  have hfrob := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree (K := F.subgroupOf N)
    (B := Subgroup.zpowers c') (restrictRep ρ N (LinearMap.ker (fixProj ρ F)) hV'N)
    hKc hBK hfpf' hchar hfixV'
  have hB : Nat.card (Subgroup.zpowers c') = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hc
  have hinvV : ∀ x : V, x ∈ Representation.invariants (ρ.comp (Subgroup.zpowers c).subtype) ↔
      ρ c x = x := fun x =>
    Representation.mem_invariants_iff_of_forall_mem_zpowers (ρ.comp (Subgroup.zpowers c).subtype)
      (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) (mem_zpowers_self_gen c) x
  have hinv' : ∀ w : LinearMap.ker (fixProj ρ F),
      w ∈ Representation.invariants ((restrictRep ρ N (LinearMap.ker (fixProj ρ F)) hV'N).comp
        (Subgroup.zpowers c').subtype) ↔ ρ c (w : V) = (w : V) := fun w => by
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
      ((restrictRep ρ N (LinearMap.ker (fixProj ρ F)) hV'N).comp (Subgroup.zpowers c').subtype)
      (⟨c', Subgroup.mem_zpowers c'⟩ : ↥(Subgroup.zpowers c')) (mem_zpowers_self_gen c') w]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hle : Module.finrank (ZMod 2) (Representation.invariants
      ((restrictRep ρ N (LinearMap.ker (fixProj ρ F)) hV'N).comp (Subgroup.zpowers c').subtype)) ≤
      Module.finrank (ZMod 2) (Representation.invariants (ρ.comp (Subgroup.zpowers c).subtype)) := by
    set I' := Representation.invariants ((restrictRep ρ N (LinearMap.ker (fixProj ρ F)) hV'N).comp
      (Subgroup.zpowers c').subtype)
    have hmap : I'.map (LinearMap.ker (fixProj ρ F)).subtype ≤
        Representation.invariants (ρ.comp (Subgroup.zpowers c).subtype) := by
      rintro x ⟨w, hw, rfl⟩
      rw [hinvV]
      exact (hinv' w).mp hw
    have hfin : Module.finrank (ZMod 2) (I'.map (LinearMap.ker (fixProj ρ F)).subtype) =
        Module.finrank (ZMod 2) I' :=
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) I').finrank_eq.symm
    rw [← hfin]
    exact Submodule.finrank_mono hmap
  rw [hB] at hfrob
  omega

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
