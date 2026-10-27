module

public import CFSG.LocalAnalysis.StandardType.GGKSmall7Defs
public import CFSG.LocalAnalysis.StandardType.GGRootSpan7
public import CFSG.LocalAnalysis.StandardType.GGRCCardJoin
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.ZS.Adapter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggKSmall7_d6_weyl (hUse : ZS.UseInput) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (h7 : Nat.card ↥Bs = 3 ^ 7) (hD : GGKSmall7D6Data Bs L K) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨V, hVadd, hVmod, ι, φD, φE, hDvec, hEvec, aD, aE, hformD, hformE, hreflD, hreflE,
    hpairD, hpairE, hAL, hAK, hcardAL⟩ := hD
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let rD : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φD i)
  let rE : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φE i)
  have hrD : ∀ i v, rD i v = v - aD i v • hDvec i := fun i v => hformD i v
  have hrE : ∀ i v, rE i v = v - aE i v • hEvec i := fun i v => hformE i v
  have hdim : Module.finrank (ZMod 3) V = 7 := by
    have hVcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 7 := by
      rw [← hVcard, hcardV, h7]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
  have hx1 : (⟨x, hx⟩ : ↥Bs) ≠ 1 := by
    intro h1
    exact l05nDD1_x_ne_one hH (by simpa using congrArg Subtype.val h1)
  have hxVne : xV ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := ι.injective (by simpa [xV] using h0)
    have h2 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  let φo : Option (Fin 6) → MulAut ↥Bs := fun o => o.elim 1 φD
  let ho : Option (Fin 6) → V := fun o => o.elim 0 hDvec
  let αo : Option (Fin 6) → Module.Dual (ZMod 3) V := fun o => o.elim 0 aD
  have hφo : ∀ o w, ggLin (p := 3) ι (φo o) w = w - αo o w • ho o := by
    intro o w
    cases o with
    | none => simp [φo, αo, ho]
    | some i => exact hformD i w
  have hLo : ∀ i j : Fin 6, αo (some i) (ho (some j)) = (CartanMatrix.D 6 i j : ZMod 3) := by
    intro i j
    simpa [αo, ho] using hpairD i j
  have hALo : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Fin 6 => φo (some i)) := by
    simpa [φo] using hAL
  have hxD : ∀ i : Fin 6, aD i xV = 0 := by
    have h := l05nDD1_alpha_x (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hH hx hφo hLo
      (ggIntCartan_D 6) hALo
    intro i
    simpa [αo, xV] using h i
  have fixD : ∀ v : V, (∀ i : Fin 6, aD i v = 0) →
      v ∈ Submodule.span (ZMod 3) ({xV} : Set V) := by
    intro v hv
    have h := l05nDD1_fix hFix hH hx hφo hALo v (fun j => by simpa [αo] using hv j)
    simpa [xV] using h
  have moves : ∃ i : Fin 6, rE i xV ≠ xV := by
    by_contra hno
    push Not at hno
    have hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
      rw [hAK]
      refine ggFixed_of_mem_closure φE (⟨x, hx⟩ : ↥Bs) ?_
      intro i
      refine (ggLin_fix_iff (p := 3) ι (φE i) (⟨x, hx⟩ : ↥Bs)).mpr ?_
      change rE i xV = xV
      rw [hno i]
    exact ggTT_not_fixed hFixK hH hx hfix
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range rD ∪ Set.range rE)
  have hA' : A' = Subgroup.closure (Set.range φD ∪ Set.range φE) := by
    change ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φD ∪ Set.range φE)
    rw [hAL, hAK, ← Subgroup.closure_union]
  have hmap : A'.map (ggLin (p := 3) ι) = A := by
    rw [hA', MonoidHom.map_closure]
    change Subgroup.closure ((ggLin (p := 3) ι) '' (Set.range φD ∪ Set.range φE)) =
      Subgroup.closure (Set.range rD ∪ Set.range rE)
    congr 1
    ext z
    constructor
    · rintro ⟨ψ, hψ | hψ, rfl⟩
      · obtain ⟨i, rfl⟩ := hψ
        exact Or.inl ⟨i, rfl⟩
      · obtain ⟨i, rfl⟩ := hψ
        exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨φD i, Or.inl ⟨i, rfl⟩, rfl⟩
      · exact ⟨φE i, Or.inr ⟨i, rfl⟩, rfl⟩
  have hA : ∀ g ∈ Subgroup.closure (Set.range rD ∪ Set.range rE),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ v, g (g v - v) = g v - v) := by
    intro g hg hcond
    have hg' : g ∈ A'.map (ggLin (p := 3) ι) := by rw [hmap]; exact hg
    obtain ⟨ψ, hψ, hψg⟩ := Subgroup.mem_map.mp hg'
    rw [← hψg] at hcond
    exact ggTT_nt_sup hH ι hψ hcond
  obtain ⟨hspan, habs⟩ := ggRootSpan7_holds (V := V) hdim hDvec hEvec aD aE rD rE xV hpairD
    hpairE hrD hrE hxVne hxD fixD moves hA
  have hgen : ZS.ReflGen 3 A := by
    rw [ZS.reflGen_iff_eq_closure_ggLinRefl]
    apply le_antisymm
    · change Subgroup.closure (Set.range rD ∪ Set.range rE) ≤
        Subgroup.closure {r : V ≃ₗ[ZMod 3] V | r ∈ A ∧ GGLinRefl r}
      apply Subgroup.closure_mono
      rintro r (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Subgroup.subset_closure (Or.inl ⟨i, rfl⟩),
          (ggRC_isReflection_iff_linRefl (p := 3) ι (φD i)).mp (hreflD i)⟩
      · exact ⟨Subgroup.subset_closure (Or.inr ⟨i, rfl⟩),
          (ggRC_isReflection_iff_linRefl (p := 3) ι (φE i)).mp (hreflE i)⟩
    · rw [Subgroup.closure_le]
      intro z hz
      exact hz.1
  have hcardA : Nat.card ↥A ≤ 3 ^ 7 * (12 * 23040) := by
    have hjoin := ggRC_card_join_le hOrb hH hx
    have h1 : Nat.card ↥A = Nat.card ↥A' := by
      rw [hmap.symm]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective A' (ggLin (p := 3) ι)
        (ggLin_injective ι)).toEquiv).symm
    calc Nat.card ↥A = Nat.card ↥A' := h1
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := hjoin
      _ = 3 ^ 7 * (12 * 23040) := by rw [h7, hcardAL]
  have hbound : 8 * Nat.card ↥A < 3 ^ 21 := by
    calc 8 * Nat.card ↥A ≤ 8 * (3 ^ 7 * (12 * 23040)) := Nat.mul_le_mul_left _ hcardA
      _ < 3 ^ 21 := by norm_num
  have hfam : ZS.Family 3 A := hUse 3 V A (by norm_num) (by omega) hgen habs
  cases hfam with
  | weyl hW =>
      exact ggRC_weylReflGroup_of_linWeyl (p := 3) ι A' (by rw [hmap]; exact hW)
  | slpm hAsl =>
      exfalso
      obtain ⟨-, hle⟩ := ZS.sl_le_and_pow_le_card_of_slpm (p := 3) hdim hAsl
      norm_num at hle hbound
      omega
  | orth Q hQ hAorth =>
      exfalso
      have horth : GGOrthType A := ZS.ggOrthType_of_orth hQ hAorth
      have hle := ZS.pow_le_card_of_ggOrthType (p := 3) (by norm_num) hdim (by omega) horth
      norm_num at hle hbound
      omega
  | orthClass Q c hQ hc hAorth =>
      exfalso
      have horth : GGOrthType A :=
        ZS.ggOrthType_of_orthClass (p := 3) (by norm_num) (by omega) hQ hc hAorth
      have hle := ZS.pow_le_card_of_ggOrthType (p := 3) (by norm_num) hdim (by omega) horth
      norm_num at hle hbound
      omega
  | gmmn f i₀ i₁ ζ m hi hm hord hAeq =>
      exfalso
      have h2 : ζ ^ 2 = 1 := by
        have hcard : Nat.card ((ZMod 3)ˣ) = 2 := by
          rw [Nat.card_eq_fintype_card, ZMod.card_units]
        have h := pow_card_eq_one' (G := ((ZMod 3)ˣ)) (x := ζ)
        rwa [hcard] at h
      have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  | g2mmn f i₀ i₁ ζ m hi hm hord hAeq =>
      exfalso
      have h2 : ζ ^ 2 = 1 := by
        have hcard : Nat.card ((ZMod 3)ˣ) = 2 := by
          rw [Nat.card_eq_fintype_card, ZMod.card_units]
        have h := pow_card_eq_one' (G := ((ZMod 3)ˣ)) (x := ζ)
        rwa [hcard] at h
      have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  | exc k hadm hfin hcard hcen hdmax hone hmodel =>
      exfalso
      have hk := ZS.ExcRow.deg_le_six k
      omega
  | h4 hp5 hfin hcard hneg hdmax hone =>
      exfalso
      omega

end CFSG.StandardType

end
