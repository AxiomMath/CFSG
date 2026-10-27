module

public import CFSG.LocalAnalysis.StandardType.GGF4N2Rank
public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusOmega
public import CFSG.GH74.E2.DirectProd
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
public import CFSG.Mathlib.GroupTheory.MulAutProd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open Module Multiplicative

theorem ggBstar_inf_selfCent_of_split
    {G : Type} [Group G] {p : ℕ} {Bs X C : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hsplit : Bs = C ⊔ (Bs ⊓ X))
    (hCX : C ≤ Subgroup.centralizer (X : Set G))
    {g : G} (hgX : g ∈ X) (hg : g ^ p = 1)
    (hc : ∀ c ∈ Bs ⊓ X, g * c = c * g) : g ∈ Bs ⊓ X := by
  have hCBs : C ≤ Bs := by rw [hsplit]; exact le_sup_left
  have hcomm : ∀ a ∈ C, ∀ c ∈ Bs ⊓ X, Commute a c := by
    intro a ha c hcm
    exact hBs.comm (hCBs ha) hcm.1
  have hgC : g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [hsplit] at hb
    obtain ⟨a, ha, c, hcm, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hb
    have hag : Commute a g := (Subgroup.mem_centralizer_iff.mp (hCX ha) g hgX).symm
    have hcg : Commute c g := (hc c hcm).symm
    exact (hag.mul_left hcg).eq
  exact ⟨hSC g hgC hg, hgX⟩

theorem ggF4N2Bstar_native_selfCent_of_inf
    {G : Type} [Group G] {Bs X : Subgroup G}
    (hsc : ∀ {g : G}, g ∈ X → g ^ 5 = 1 →
      (∀ c ∈ Bs ⊓ X, g * c = c * g) → g ∈ Bs ⊓ X)
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (e : ↥X ≃* ↥(orthDerived Q)) :
    let E := ((Bs ⊓ X).subgroupOf X).map e.toMonoidHom
    ∀ g : ↥(orthDerived Q), (∀ c ∈ E, g * c = c * g) → g ^ 5 = 1 → g ∈ E := by
  dsimp only
  intro g hc hg5
  let gX : X := e.symm g
  have hgX5 : (gX : G) ^ 5 = 1 := by
    have hX5 : gX ^ 5 = 1 := by simpa [gX] using congrArg e.symm hg5
    exact congrArg Subtype.val hX5
  have hgXC : ∀ c ∈ Bs ⊓ X, (gX : G) * c = c * (gX : G) := by
    intro c hcm
    let cX : X := ⟨c, hcm.2⟩
    have hec : e cX ∈ ((Bs ⊓ X).subgroupOf X).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨cX, hcm, rfl⟩
    have h := hc (e cX) hec
    have hXcomm : gX * cX = cX * gX := by
      apply e.injective
      simpa only [map_mul, gX, MulEquiv.apply_symm_apply] using h
    exact congrArg Subtype.val hXcomm
  have hgP := hsc gX.2 hgX5 hgXC
  exact Subgroup.mem_map.mpr ⟨gX, hgP, e.apply_symm_apply g⟩

theorem ggF4N2Bstar_internal_torus_of_selfCent
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBsEl : IsElemAbelian 5 Bs) (hcard : Nat.card ↥(Bs ⊓ X) = 5 ^ 3)
    (hsc : ∀ {g : G}, g ∈ X → g ^ 5 = 1 →
      (∀ c ∈ Bs ⊓ X, g * c = c * g) → g ∈ Bs ⊓ X)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hK : Nat.card K = 4) (hV : finrank K V = 8)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (e : ↥X ≃* ↥(orthDerived Q)) :
    ∃ τ : (Fin 3 → Multiplicative (ZMod 5)) →* ↥X,
      Function.Injective τ ∧ τ.range = (Bs ⊓ X).subgroupOf X ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ w : X, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) ∧
      (∀ i : Fin 3, ∃ w : X, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) ∧
      (∀ n : X, n ∈ Subgroup.normalizer (((Bs ⊓ X).subgroupOf X : Subgroup X) : Set X) →
        ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 5),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', n * τ f * n⁻¹ = τ f' →
            ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P : Subgroup X := (Bs ⊓ X).subgroupOf X
  let E : Subgroup ↥(orthDerived Q) := P.map e.toMonoidHom
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    apply congrArg e
    exact Subtype.ext (hBsEl.comm ha.1 hb.1)
  have hEab : IsElemAbelian 5 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have ha5 : a ^ 5 = 1 := Subtype.ext (hBsEl.2 a ha.1)
    rw [← map_pow, ha5, map_one]
  have hEcard : Nat.card E = 5 ^ 3 := by
    calc Nat.card E = Nat.card P :=
          (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
      _ = Nat.card ↥(Bs ⊓ X) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ X ≤ X)).toEquiv
      _ = 5 ^ 3 := hcard
  obtain ⟨r, τ, hτinj, hτE, hperm, -, hnorm, hW⟩ :=
    OrthTorus.exists_torus_orthDerived Nat.prime_five (by decide) (Or.inr (by norm_num [hK]))
      hQ hT E hEab (by rw [hEcard]) (ggF4N2Bstar_native_selfCent_of_inf hsc e)
  have hdom : Nat.card (Fin r → Multiplicative (ZMod 5)) = 5 ^ r := by
    rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hr : r = 3 := Nat.pow_right_injective (by decide : 2 ≤ 5) (by
    change 5 ^ r = 5 ^ 3
    calc 5 ^ r = Nat.card (Fin r → Multiplicative (ZMod 5)) := hdom.symm
      _ = Nat.card τ.range := Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv
      _ = Nat.card E := by rw [hτE]
      _ = 5 ^ 3 := hEcard)
  subst r
  have hsign : ∀ i : Fin 3, ∃ w : ↥(orthDerived Q), ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f) := by
    rcases hW with ⟨-, hdim⟩ | ⟨-, hsgn⟩
    · omega
    · exact hsgn
  let τL : (Fin 3 → Multiplicative (ZMod 5)) →* X := e.symm.toMonoidHom.comp τ
  have hτLP : τL.range = P := by
    change (e.symm.toMonoidHom.comp τ).range = P
    rw [MonoidHom.range_comp, hτE]
    change (P.map e.toMonoidHom).map e.symm.toMonoidHom = P
    rw [Subgroup.map_map]
    simp
  refine ⟨τL, e.symm.injective.comp hτinj, hτLP, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    exact ⟨e.symm w, fun f => by simpa [τL] using congrArg e.symm (hw f)⟩
  · intro i
    obtain ⟨w, hw⟩ := hsign i
    exact ⟨e.symm w, fun f => by simpa [τL] using congrArg e.symm (hw f)⟩
  · intro n hn
    have hnE : ∀ a ∈ E, e n * a * (e n)⁻¹ ∈ E := by
      rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.mem_map.mpr ⟨n * a * n⁻¹, ?_, by simp⟩
      have h := (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
      change n * a * n⁻¹ ∈ (Bs ⊓ X).subgroupOf X
      rw [← h]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨π, ε, hε, hcoords⟩ := hnorm (e n) hnE
    refine ⟨π, ε, hε, fun f f' h i => ?_⟩
    have h' := congrArg e h
    have heq : e n * τ f * (e n)⁻¹ = τ f' := by simpa [τL] using h'
    exact hcoords f f' heq i

theorem ggF4N2Bstar_coordinates_of_split
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {x : G}
    (hBEl : IsElemAbelian 5 Bs) (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hBs : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ X))
    (hdisj : Disjoint (Subgroup.zpowers x) (Bs ⊓ X))
    (τ : (Fin 3 → Multiplicative (ZMod 5)) →* X)
    (hτinj : Function.Injective τ) (hτP : τ.range = (Bs ⊓ X).subgroupOf X) :
    ∃ χ : Multiplicative (ZMod 5) ≃* Subgroup.zpowers x,
      χ (Multiplicative.ofAdd 1) = ⟨x, Subgroup.mem_zpowers x⟩ ∧
    ∃ κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs,
      ((κ (Multiplicative.ofAdd 1, 1) : Bs) : G) = x ∧
      (∀ f, ((κ (1, f) : Bs) : G) = (τ f : G)) ∧
      ∀ m f, ((κ (m, f) : Bs) : G) = (χ m : G) * (τ f : G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hXBs : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr hxBs
  have hxc : Nat.card (Subgroup.zpowers x) = 5 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hBEl.2 x hxBs) hx1
  let xX : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
  have hxgen : ∀ a : Subgroup.zpowers x, ∃ n : ℤ, xX ^ n = a := by
    intro a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
    exact ⟨n, Subtype.ext hn⟩
  let χ : Multiplicative (ZMod 5) ≃* Subgroup.zpowers x := zmodMulEquivOfGenerator hxgen hxc
  let eT : (Fin 3 → Multiplicative (ZMod 5)) ≃* ↥(Bs ⊓ X) :=
    (MonoidHom.ofInjective hτinj).trans ((MulEquiv.subgroupCongr hτP).trans
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ X ≤ X)))
  have hc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Bs ⊓ X, a * b = b * a := by
    intro a ha b hb
    exact hBEl.comm (hXBs ha) hb.1
  let eSup := CFSG.GH74.E2.prodSupEquiv (Subgroup.zpowers x) (Bs ⊓ X) hc
    (disjoint_iff.mp hdisj)
  let κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs :=
    (χ.prodCongr eT).trans (eSup.trans (MulEquiv.subgroupCongr hBs.symm))
  have heT (f : Fin 3 → Multiplicative (ZMod 5)) : (eT f : G) = (τ f : G) := by
    rfl
  have hκ (m : Multiplicative (ZMod 5)) (f : Fin 3 → Multiplicative (ZMod 5)) :
      ((κ (m, f) : Bs) : G) = (χ m : G) * (τ f : G) := by
    change ((eSup (χ m, eT f) : ↥(Subgroup.zpowers x ⊔ (Bs ⊓ X))) : G) =
      (χ m : G) * (τ f : G)
    rw [CFSG.GH74.E2.prodSupEquiv_apply]
    rw [heT]
  have hχ : χ (Multiplicative.ofAdd 1) = xX :=
    zmodMulEquivOfGenerator_apply_ofAdd_one hxgen hxc
  refine ⟨χ, hχ, κ, ?_, ?_, hκ⟩
  ·
    rw [hκ, hχ, map_one, Subgroup.coe_one, mul_one]
  · intro f
    rw [hκ, map_one, Subgroup.coe_one, one_mul]

section OriginalTorus

theorem ggF4N2Bstar_inf_L_selfCent
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    {g : G} (hgL : g ∈ L) (hg5 : g ^ 5 = 1)
    (hc : ∀ c ∈ Bs ⊓ L, g * c = c * g) : g ∈ Bs ⊓ L := by
  obtain ⟨hsplit, _⟩ := ggF4N2Bstar_split hR hL
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := hR.1.1
  have hXC : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
    apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  exact ggBstar_inf_selfCent_of_split hR.1.2.1.2.1 hR.1.2.1.2.2.2 hsplit hXC hgL hg5 hc

theorem ggF4N2Bstar_internal_torus
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hK : Nat.card K = 4) (hV : finrank K V = 8)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (e : ↥L ≃* ↥(orthDerived Q)) :
    ∃ τ : (Fin 3 → Multiplicative (ZMod 5)) →* ↥L,
      Function.Injective τ ∧ τ.range = (Bs ⊓ L).subgroupOf L ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ w : L, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) ∧
      (∀ i : Fin 3, ∃ w : L, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) ∧
      (∀ n : L, n ∈ Subgroup.normalizer (((Bs ⊓ L).subgroupOf L : Subgroup L) : Set L) →
        ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 5),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', n * τ f * n⁻¹ = τ f' →
            ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) := by
  exact ggF4N2Bstar_internal_torus_of_selfCent hR.1.2.1.2.1
    (ggF4N2Bstar_inf_L_card hR hL)
    (fun hgL hg5 hc => ggF4N2Bstar_inf_L_selfCent hR hL hgL hg5 hc) hK hV hQ hT e

theorem ggF4N2Bstar_coordinates_of_internal_torus
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (τ : (Fin 3 → Multiplicative (ZMod 5)) →* L)
    (hτinj : Function.Injective τ) (hτP : τ.range = (Bs ⊓ L).subgroupOf L) :
    ∃ χ : Multiplicative (ZMod 5) ≃* Subgroup.zpowers x,
      χ (Multiplicative.ofAdd 1) = ⟨x, Subgroup.mem_zpowers x⟩ ∧
    ∃ κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs,
      ((κ (Multiplicative.ofAdd 1, 1) : Bs) : G) = x ∧
      (∀ f, ((κ (1, f) : Bs) : G) = (τ f : G)) ∧
      ∀ m f, ((κ (m, f) : Bs) : G) = (χ m : G) * (τ f : G) := by
  obtain ⟨hsplit, hdisj⟩ := ggF4N2Bstar_split hR hL
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := hR.1.1
  exact ggF4N2Bstar_coordinates_of_split hR.1.2.1.2.1 (hR.1.2.1.1 hS.2.1) hS.2.2.1
    hsplit hdisj τ hτinj hτP

end OriginalTorus

theorem ggIsReflection_congr_prod_id
    {G : Type} [Group G] {Bs : Subgroup G} {C T : Type} [Group C] [Group T]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (κ : C × T ≃* Bs) (a : MulAut T)
    (ha2 : a ^ 2 = 1) (hcard : Nat.card {t : T // a t = t} * p = Nat.card T) :
    GGIsReflection p (MulAut.congr κ (MulEquiv.prodCongr (MulEquiv.refl C) a)) := by
  have hprod2 : (MulEquiv.prodCongr (MulEquiv.refl C) a : MulAut (C × T)) ^ 2 = 1 := by
    change (MulAut.prodRightHom (G := C) a) ^ 2 = 1
    rw [← map_pow, ha2, map_one]
  refine ggSpSigned_ggIsReflection_congr hp hp2 κ hprod2 ?_
  change Nat.card {v : C × T // MulAut.prodRightHom a v = v} * p = Nat.card (C × T)
  rw [MulAut.card_fixed_prodRightHom, Nat.card_prod, mul_assoc, hcard]

theorem ggF4N2Bstar_sgn_reflection
    {G : Type} [Group G] {Bs : Subgroup G}
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs) (i : Fin 3) :
    GGIsReflection 5 (MulAut.congr κ
      (MulEquiv.prodCongr (MulEquiv.refl (Multiplicative (ZMod 5))) (SpCoord.sgnAut i))) :=
  ggIsReflection_congr_prod_id Nat.prime_five (by decide) κ (SpCoord.sgnAut i)
    (SpCoord.sgnAut_sq i) (SpCoord.card_fix_sgnAut Nat.prime_five (by decide) i)

theorem ggF4N2Bstar_swap_reflection
    {G : Type} [Group G] {Bs : Subgroup G}
    (κ : (Multiplicative (ZMod 5) × (Fin 3 → Multiplicative (ZMod 5))) ≃* Bs)
    {i j : Fin 3} (hij : i ≠ j) :
    GGIsReflection 5 (MulAut.congr κ
      (MulEquiv.prodCongr (MulEquiv.refl (Multiplicative (ZMod 5)))
        (SpCoord.permAut (Equiv.swap i j)))) :=
  ggIsReflection_congr_prod_id Nat.prime_five (by decide) κ _
    (SpCoord.permAut_swap_sq i j) (SpCoord.card_fix_permAut_swap Nat.prime_five (by decide) hij)

theorem ggConjAut_congr_prod_of_conj
    {G : Type} [Group G] {H Bs : Subgroup G}
    {C T : Type} [Group C] [Group T]
    (κ : C × T ≃* Bs) (c : C →* G) (τ : T →* H)
    (hκ : ∀ m f, ((κ (m, f) : Bs) : G) = c m * (τ f : G))
    (w : H) (a : MulAut T) (hc : ∀ m, Commute (c m) (w : G))
    (hw : ∀ f, w * τ f * w⁻¹ = τ (a f)) :
    ∃ hwN : (w : G) ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr κ (MulEquiv.prodCongr (MulEquiv.refl C) a) = ggConjAut Bs hwN := by
  let φ : MulAut Bs := MulAut.congr κ (MulEquiv.prodCongr (MulEquiv.refl C) a)
  have hact (m : C) (f : T) :
      (w : G) * (κ (m, f) : G) * (w : G)⁻¹ = (κ (m, a f) : G) := by
    rw [hκ m f, hκ m (a f)]
    have hwf : (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (a f) : G) :=
      congrArg Subtype.val (hw f)
    calc (w : G) * (c m * (τ f : G)) * (w : G)⁻¹ =
          ((w : G) * c m) * (τ f : G) * (w : G)⁻¹ := by group
      _ = (c m * (w : G)) * (τ f : G) * (w : G)⁻¹ := by rw [(hc m).eq.symm]
      _ = c m * ((w : G) * (τ f : G) * (w : G)⁻¹) := by group
      _ = c m * (τ (a f) : G) := by rw [hwf]
  have hφ (b : Bs) : ((φ b : Bs) : G) = (w : G) * b * (w : G)⁻¹ := by
    obtain ⟨⟨m, f⟩, rfl⟩ := κ.surjective b
    change (κ (MulEquiv.prodCongr (MulEquiv.refl C) a (κ.symm (κ (m, f)))) : G) = _
    rw [κ.symm_apply_apply]
    exact (hact m f).symm
  have hwN : (w : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    apply Set.ext
    intro b
    constructor
    · rintro ⟨d, hd, rfl⟩
      change (w : G) * d * (w : G)⁻¹ ∈ Bs
      rw [← hφ ⟨d, hd⟩]
      exact (φ ⟨d, hd⟩).2
    · intro hb
      obtain ⟨d, hd⟩ := φ.surjective (⟨b, hb⟩ : Bs)
      refine ⟨(d : G), d.2, ?_⟩
      change (w : G) * d * (w : G)⁻¹ = b
      rw [← hφ d, hd]
  refine ⟨hwN, ?_⟩
  apply MulEquiv.ext
  intro b
  exact Subtype.ext (hφ b)

theorem ggInduced_congr_prod_of_conj
    {G : Type} [Group G] {H Bs : Subgroup G}
    {C T : Type} [Group C] [Group T]
    (κ : C × T ≃* Bs) (c : C →* G) (τ : T →* H)
    (hκ : ∀ m f, ((κ (m, f) : Bs) : G) = c m * (τ f : G))
    (w : H) (a : MulAut T) (hc : ∀ m, Commute (c m) (w : G))
    (hw : ∀ f, w * τ f * w⁻¹ = τ (a f)) :
    MulAut.congr κ (MulEquiv.prodCongr (MulEquiv.refl C) a) ∈ ggInduced H Bs := by
  obtain ⟨hwN, heq⟩ := ggConjAut_congr_prod_of_conj κ c τ hκ w a hc hw
  rw [heq]
  exact ggConjAut_mem_ggInduced w.2 hwN

end CFSG.StandardType

end
