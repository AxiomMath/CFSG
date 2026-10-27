module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

theorem zeta_pow_val_sub_mul {G : Type*} [Group G] {ζ : G} (hζ : ζ ^ 3 = 1) (a c : ZMod 3)
    (n : ℤ) : ζ ^ (a - c * (n : ZMod 3)).val = ζ ^ a.val * (ζ ^ c.val) ^ (-n) := by
  have hcast : (((a - c * (n : ZMod 3)).val : ℤ) : ZMod 3) =
      (((a.val : ℤ) - (c.val : ℤ) * n : ℤ) : ZMod 3) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hmod : ((a - c * (n : ZMod 3)).val : ℤ) % 3 =
      ((a.val : ℤ) - (c.val : ℤ) * n) % 3 :=
    (ZMod.intCast_eq_intCast_iff' _ _ 3).1 hcast
  calc ζ ^ (a - c * (n : ZMod 3)).val
      = ζ ^ ((a - c * (n : ZMod 3)).val : ℤ) := (zpow_natCast ζ _).symm
    _ = ζ ^ (((a - c * (n : ZMod 3)).val : ℤ) % 3) := zpow_eq_zpow_emod' _ hζ
    _ = ζ ^ (((a.val : ℤ) - (c.val : ℤ) * n) % 3) := by rw [hmod]
    _ = ζ ^ ((a.val : ℤ) - (c.val : ℤ) * n) := (zpow_eq_zpow_emod' _ hζ).symm
    _ = ζ ^ ((a.val : ℤ) + (c.val : ℤ) * (-n)) := by
        congr 1
        ring
    _ = ζ ^ (a.val : ℤ) * ζ ^ ((c.val : ℤ) * (-n)) := zpow_add _ _ _
    _ = ζ ^ (a.val : ℤ) * (ζ ^ (c.val : ℤ)) ^ (-n) := by rw [zpow_mul]
    _ = ζ ^ a.val * (ζ ^ c.val) ^ (-n) := by rw [zpow_natCast, zpow_natCast]

theorem zeta_pow_val_injective {G : Type*} [Group G] {ζ : G} (hζ : ζ ^ 3 = 1) (h1 : ζ ≠ 1) :
    Function.Injective fun a : ZMod 3 => ζ ^ a.val := by
  have hdvd : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one hζ
  have hne : orderOf ζ ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf ζ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  intro a b hab
  have h : ζ ^ (a.val : ℤ) = ζ ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact hab
  have hmod : (a.val : ℤ) ≡ (b.val : ℤ) [ZMOD (orderOf ζ : ℤ)] :=
    zpow_eq_zpow_iff_modEq.1 h
  rw [hord] at hmod
  have heq : (a.val : ℤ) % 3 = (b.val : ℤ) % 3 := Int.ModEq.eq hmod
  rw [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ a.val) (by exact_mod_cast ZMod.val_lt a),
    Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ b.val) (by exact_mod_cast ZMod.val_lt b)] at heq
  exact ZMod.val_injective 3 (by exact_mod_cast heq)


namespace ExcCoordDatum

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} (d : ExcCoordDatum S T₀ m)
include d

theorem le_torusGroup : T₀ ≤ torusGroup τ L :=
  fun _ ht =>
    (inf_le_left : S.D.torus ≤ torusGroup τ L) (d.le_fullThreeTorus ht).1

theorem exists_rootDiagUnit (t : ↥T₀) : ∃ b, (t : ModGL τ L) = rootDiagUnit τ b :=
  exists_rootDiagUnit_eq_of_mem_torusGroup (d.le_torusGroup t.2)

theorem weylTuple_reflection_mem (i : ExcRaw.Root m) {b : Fin τ.rank → Lˣ}
    (hb : rootDiagUnit τ b ∈ T₀) :
    ∃ h : rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b) ∈ T₀,
      d.coord (Additive.ofMul ⟨_, h⟩) =
        ExcRaw.reflection m i (d.coord (Additive.ofMul ⟨_, hb⟩)) := by
  classical
  set x : ExcRaw.V m := d.coord (Additive.ofMul ⟨rootDiagUnit τ b, hb⟩) with hx
  set u : ExcRaw.V m := ExcRaw.reflection m i x with hu
  set t'' : ↥T₀ := Additive.toMul (d.coord.symm u) with ht''
  have hcoord : d.coord (Additive.ofMul t'') = u := by
    rw [ht'', ofMul_toMul]
    exact d.coord.apply_symm_apply u
  obtain ⟨b'', hb''⟩ := d.exists_rootDiagUnit t''
  have hroot : ∀ j, rootChar b'' (d.γ j) =
      rootChar (weylTuple (rootReflection (d.γ i)) b) (d.γ j) := by
    intro j
    have hrootu : ExcRaw.root m j u =
        ExcRaw.root m j x - ExcRaw.root m i x * (ExcRaw.pairing m j i : ZMod 3) := by
      rw [hu, ExcRaw.reflection_apply, map_sub, map_smul, ExcRaw.pairing_eq, smul_eq_mul]
    rw [d.rootChar_eq t'' b'' hb'' j, hcoord]
    rw [rootChar_weylTuple, rootReflection_inv (d.isRoot i),
      rootReflection_smul (d.isRoot i), rootChar_sub, rootChar_zsmul]
    rw [← zpow_neg, ← d.pairing_eq j i]
    rw [d.rootChar_eq (⟨rootDiagUnit τ b, hb⟩ : ↥T₀) b rfl j,
      d.rootChar_eq (⟨rootDiagUnit τ b, hb⟩ : ↥T₀) b rfl i]
    rw [← hx, hrootu]
    exact zeta_pow_val_sub_mul d.ζ_pow_three (ExcRaw.root m j x) (ExcRaw.root m i x)
      (ExcRaw.pairing m j i)
  have hb''b : b'' = weylTuple (rootReflection (d.γ i)) b := by
    funext k
    have hsingle : ∀ c : Fin τ.rank → Lˣ, rootChar c (Pi.single k 1) = c k := by
      intro c
      simpa using rootChar_nsmul_single c k 1
    rw [← hsingle b'', ← hsingle (weylTuple (rootReflection (d.γ i)) b)]
    obtain ⟨j, hj | hj⟩ := d.exists_eq (Pi.single k 1) (isRoot_single τ k)
    · rw [hj]
      exact hroot j
    · have hneg : ∀ c : Fin τ.rank → Lˣ,
          rootChar c (-(d.γ j)) = (rootChar c (d.γ j))⁻¹ := by
        intro c
        have h := rootChar_sub c 0 (d.γ j)
        rw [zero_sub, rootChar_zero, one_mul] at h
        exact h
      rw [hj, hneg b'', hneg (weylTuple (rootReflection (d.γ i)) b), hroot j]
  have hmem : rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b) ∈ T₀ := by
    rw [← hb''b, ← hb'']
    exact t''.2
  refine ⟨hmem, ?_⟩
  have ht_eq :
      (⟨rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b), hmem⟩ : ↥T₀) = t'' := by
    apply Subtype.ext
    change rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b) = (t'' : ModGL τ L)
    rw [← hb''b]
    exact hb''.symm
  have hcoord2 : d.coord (Additive.ofMul
      ⟨rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b), hmem⟩) = u := by
    rw [ht_eq, hcoord]
  rw [hcoord2, hu, hx]

theorem exists_weylTuple_mem (w : WeylGroup τ) :
    ∃ M ∈ ExcRaw.ambientNormalizer m, ∀ (b : Fin τ.rank → Lˣ) (hb : rootDiagUnit τ b ∈ T₀),
      ∃ h : rootDiagUnit τ (weylTuple w b) ∈ T₀,
        d.coord (Additive.ofMul ⟨_, h⟩) = M (d.coord (Additive.ofMul ⟨_, hb⟩)) := by
  induction w using (coxeterSystem τ).simple_induction with
  | simple k =>
      have hs : rootReflection (Pi.single k 1) = simple τ k := by
        have h := rootReflection_eq_conj (τ := τ) (β := Pi.single k 1) (w := 1)
          (j := k) (by simp)
        simpa using h
      obtain ⟨i, hi⟩ := d.exists_eq (Pi.single k 1) (isRoot_single τ k)
      have hw : simple τ k = rootReflection (d.γ i) := by
        rcases hi with hi | hi
        · rw [← hs, hi]
        · rw [← hs, hi, rootReflection_neg (d.isRoot i)]
      refine ⟨ExcRaw.reflection m i, Subgroup.subset_closure ⟨i, rfl⟩, fun b hb => ?_⟩
      change ∃ h : rootDiagUnit τ (weylTuple (simple τ k) b) ∈ T₀,
        d.coord (Additive.ofMul ⟨_, h⟩) =
          ExcRaw.reflection m i (d.coord (Additive.ofMul ⟨_, hb⟩))
      rw [hw]
      exact d.weylTuple_reflection_mem i hb
  | one =>
      refine ⟨1, (ExcRaw.ambientNormalizer m).one_mem, ?_⟩
      intro b hb
      rw [weylTuple_one]
      exact ⟨hb, by simp⟩
  | mul w w' ihw ihw' =>
      obtain ⟨M, hM, hMprop⟩ := ihw
      obtain ⟨M', hM', hM'prop⟩ := ihw'
      refine ⟨M * M', (ExcRaw.ambientNormalizer m).mul_mem hM hM', ?_⟩
      intro b hb
      obtain ⟨h', hcoord'⟩ := hM'prop b hb
      obtain ⟨h'', hcoord''⟩ := hMprop (weylTuple w' b) h'
      rw [← weylTuple_weylTuple]
      exact ⟨h'', hcoord''.trans (by rw [hcoord', LinearEquiv.mul_apply])⟩

section Rational


theorem rootSL2_mem_normalizer (hS : NegLangTwo S) (i : ExcRaw.Root m) :
    rootSL2 τ L (d.γ i) WSL ∈ Subgroup.normalizer (T₀ : Set (ModGL τ L)) := by
  have hγ : IsRoot τ (d.γ i) := d.isRoot i
  have hchar : ((2 : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rwa [hS.1] at h
  have : CharP L 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by simpa using hchar)
  have hg2 : rootSL2 τ L (d.γ i) WSL * rootSL2 τ L (d.γ i) WSL = 1 :=
    rootWeylSL2_mul_self_of_charTwo (d.γ i)
  have hginv : (rootSL2 τ L (d.γ i) WSL)⁻¹ = rootSL2 τ L (d.γ i) WSL :=
    inv_eq_of_mul_eq_one_right hg2
  have hforward : ∀ t : ModGL τ L, t ∈ T₀ →
      rootSL2 τ L (d.γ i) WSL * t * (rootSL2 τ L (d.γ i) WSL)⁻¹ ∈ T₀ := by
    intro t ht
    obtain ⟨b, hb⟩ := d.exists_rootDiagUnit ⟨t, ht⟩
    have hb' : t = rootDiagUnit τ b := hb
    rw [hb', rootWeylSL2_conj_rootDiagUnit S hγ b]
    exact (d.weylTuple_reflection_mem (b := b) i (by rw [← hb']; exact ht)).choose
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨hforward t, ?_⟩
  intro ht
  have h := hforward (rootSL2 τ L (d.γ i) WSL * t *
    (rootSL2 τ L (d.γ i) WSL)⁻¹) ht
  have hcancel : rootSL2 τ L (d.γ i) WSL *
      (rootSL2 τ L (d.γ i) WSL * t * (rootSL2 τ L (d.γ i) WSL)⁻¹) *
        (rootSL2 τ L (d.γ i) WSL)⁻¹ = t := by
    rw [hginv]
    calc rootSL2 τ L (d.γ i) WSL *
          (rootSL2 τ L (d.γ i) WSL * t * rootSL2 τ L (d.γ i) WSL) *
            rootSL2 τ L (d.γ i) WSL
        = (rootSL2 τ L (d.γ i) WSL * rootSL2 τ L (d.γ i) WSL) * t *
            (rootSL2 τ L (d.γ i) WSL * rootSL2 τ L (d.γ i) WSL) := by group
      _ = t := by rw [hg2, one_mul, mul_one]
  rwa [hcancel] at h

theorem ggLin_ggConjAut_rootSL2 (hS : NegLangTwo S) (i : ExcRaw.Root m) :
    ggLin (p := 3) d.coord (ggConjAut T₀ (d.rootSL2_mem_normalizer hS i)) =
      ExcRaw.reflection m i := by
  have hγ : IsRoot τ (d.γ i) := d.isRoot i
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨t, rfl⟩ := d.coord.surjective v
  rw [← ofMul_toMul t, ggLin_apply_ofMul]
  obtain ⟨b, hb⟩ := d.exists_rootDiagUnit (Additive.toMul t)
  have hbT : rootDiagUnit τ b ∈ T₀ := by
    rw [← hb]
    exact (Additive.toMul t).2
  obtain ⟨hmem, hcoord⟩ := d.weylTuple_reflection_mem (b := b) i hbT
  have hφ : ((ggConjAut T₀ (d.rootSL2_mem_normalizer hS i) (Additive.toMul t) : ↥T₀) :
      ModGL τ L) = rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b) := by
    rw [ggConjAut_apply, hb, rootWeylSL2_conj_rootDiagUnit S hγ b]
  have hsub : ggConjAut T₀ (d.rootSL2_mem_normalizer hS i) (Additive.toMul t) =
      ⟨rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b), hmem⟩ :=
    Subtype.ext hφ
  have ht_eq : (Additive.toMul t : ↥T₀) = ⟨rootDiagUnit τ b, hbT⟩ := Subtype.ext hb
  calc d.coord (Additive.ofMul (ggConjAut T₀ (d.rootSL2_mem_normalizer hS i)
        (Additive.toMul t)))
      = d.coord (Additive.ofMul
          ⟨rootDiagUnit τ (weylTuple (rootReflection (d.γ i)) b), hmem⟩) := by rw [hsub]
    _ = ExcRaw.reflection m i
          (d.coord (Additive.ofMul ⟨rootDiagUnit τ b, hbT⟩)) := hcoord
    _ = ExcRaw.reflection m i (d.coord (Additive.ofMul (Additive.toMul t))) := by
        rw [← ht_eq]

theorem reflection_mem_map_ggAutomizer_of_mem (hS : NegLangTwo S) {X : Subgroup (ModGL τ L)}
    (i : ExcRaw.Root m) (hX : rootSL2 τ L (d.γ i) WSL ∈ X) :
    ExcRaw.reflection m i ∈ (ggAutomizer X T₀).map (ggLin (p := 3) d.coord) :=
  Subgroup.mem_map.2 ⟨ggConjAut T₀ (d.rootSL2_mem_normalizer hS i),
    ggConjAut_mem_ggAutomizer hX (d.rootSL2_mem_normalizer hS i), d.ggLin_ggConjAut_rootSL2 hS i⟩

theorem reflection_mem_map_ggAutomizer (hS : NegLangTwo S)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : ExcRaw.Root m) :
    ExcRaw.reflection m i ∈ (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) :=
  d.reflection_mem_map_ggAutomizer_of_mem hS i
    (rootWeylSL2_mem_Γ_of_rho_neg S hτ (by rw [hS.1, pow_one]) hS.2.1 (d.isRoot i)
      (hS.2.2 _ (d.isRoot i)))

theorem ambientNormalizer_le_map_ggAutomizer (hS : NegLangTwo S)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ExcRaw.ambientNormalizer m ≤ (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) :=
  (Subgroup.closure_le _).2 fun _ ⟨i, hi⟩ => hi ▸ d.reflection_mem_map_ggAutomizer hS hτ i

end Rational

end ExcCoordDatum

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
