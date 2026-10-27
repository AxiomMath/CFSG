module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
import CFSG.LocalAnalysis.StandardType.KGLangTorusModel
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcGlue

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

private theorem kgLangInnerAux_isElemAbelian_of_le {p : ℕ} {G : Type*} [Group G]
    {A B : Subgroup G} (hB : IsElemAbelian p B) (hAB : A ≤ B) : IsElemAbelian p A := by
  refine ⟨?_, ?_⟩
  · refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
    show (a : G) * b = (b : G) * a
    letI : IsMulCommutative B := hB.1
    exact congrArg Subtype.val (mul_comm' (⟨a, hAB a.2⟩ : B) (⟨b, hAB b.2⟩ : B))
  · intro x hx
    exact hB.2 x (hAB hx)

private theorem kgLangInnerAux_isElemAbelian_map {p : ℕ} {G N : Type*} [Group G] [Group N]
    (f : G →* N) {A : Subgroup G} (hA : IsElemAbelian p A) :
    IsElemAbelian p (Subgroup.map f A) := by
  refine ⟨?_, ?_⟩
  · refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hbeq⟩ := Subgroup.mem_map.mp b.2
    change (a : N) * (b : N) = (b : N) * (a : N)
    rw [← haeq, ← hbeq, ← map_mul, ← map_mul]
    letI : IsMulCommutative A := hA.1
    exact congrArg f (congrArg Subtype.val (mul_comm' (⟨a', ha'⟩ : A) (⟨b', hb'⟩ : A)))
  · intro x hx
    obtain ⟨x', hx', hxeq⟩ := Subgroup.mem_map.mp hx
    rw [← hxeq, ← map_pow, hA.2 x' hx', map_one]

private theorem kgLangInnerAux_conj_mul_apply {R : Type*} [Group R] (u : MulAut R) (r : R) :
    MulAut.conj (u r) = u * MulAut.conj r * u⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem kgLangInnerAux_conj_injective {R : Type*} [Group R]
    (hcenter : Subgroup.center R = ⊥) : Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxcenter : x ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun f : MulAut R => f g) hx
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * x = (x * g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  exact Subgroup.mem_bot.mp (hcenter ▸ hxcenter)

private theorem kgLangInnerAux_eq_of_conj {R G : Type*} [Group R] [Group G]
    (ι : R →* G) (hG5 : ∀ g : G, (∀ r, g * ι r = ι r * g) → g = 1)
    {u : MulAut R} {h₁ h₂ : G}
    (hh₁ : ∀ r, ι (u r) = h₁ * ι r * h₁⁻¹) (hh₂ : ∀ r, ι (u r) = h₂ * ι r * h₂⁻¹) :
    h₁ = h₂ := by
  have hcomm : ∀ r, (h₂⁻¹ * h₁) * ι r = ι r * (h₂⁻¹ * h₁) := by
    intro r
    have heq : h₁ * ι r * h₁⁻¹ = h₂ * ι r * h₂⁻¹ := by rw [← hh₁ r, ← hh₂ r]
    calc (h₂⁻¹ * h₁) * ι r
        = h₂⁻¹ * (h₁ * ι r * h₁⁻¹) * h₁ := by group
      _ = h₂⁻¹ * (h₂ * ι r * h₂⁻¹) * h₁ := by rw [heq]
      _ = ι r * (h₂⁻¹ * h₁) := by group
  exact (inv_mul_eq_one.mp (hG5 (h₂⁻¹ * h₁) hcomm)).symm

private theorem kgLangInnerAux_endPow_succ {G : Type*} [Monoid G] (S : G →* G) (n : ℕ) (x : G) :
    endPow S (n + 1) x = S (endPow S n x) := by
  rw [endPow_apply, endPow_apply, Function.iterate_succ_apply']

theorem kgLangTorusMPart_of_inner {p : ℕ} (hp : p.Prime) {R : Type} [Group R] [Finite R]
    {I F : Set (MulAut R)} (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hcyc : GGRawFieldCycW p R I F) (hconj : GGRawFieldConj p R I F)
    (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hG1 : ∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r)
    (hT : ∀ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I → ∀ f ∈ F, orderOf f = p →
      KGLangTorusInput p J (MulAut.conj f).toMonoidHom)
    (hZ : ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R),
      commutator (HopfCover R) = ⊤ → Nat.Coprime (Nat.card (Subgroup.center (HopfCover R))) p) :
    KGLangTorusMPart p R I F := by
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  haveI : Finite (HopfCover R) := hfin
  obtain ⟨J, S, hJI, hJS, hJn, hcycquot, hS⟩ := hcyc hs hna
  have hJmem : ∀ u : MulAut R, u ∈ J ↔ u ∈ I := fun u => by
    change u ∈ (J : Set (MulAut R)) ↔ u ∈ I
    rw [hJI]
  have hcommR : ¬ IsMulCommutative R := by
    intro h
    obtain ⟨a, b, hab⟩ := hna
    exact hab (isMulCommutative_iff.mp h a b)
  have hcenterR : Subgroup.center R = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center R) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hcommR
  have hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    kgLangInnerAux_conj_injective hcenterR
  let ι : R →* ↥J :=
    { toFun := fun r => ⟨MulAut.conj r, (hJmem _).mpr (hinn r)⟩
      map_one' := Subtype.ext (map_one MulAut.conj)
      map_mul' := fun r s => Subtype.ext (map_mul MulAut.conj r s) }
  have hι : Function.Injective ι := by
    intro r s hrs
    exact hconj_inj (congrArg Subtype.val hrs)
  have hG1' : ∀ g : ↥J, ∀ k : ℕ, g ^ (p ^ k) = 1 → g ∈ ι.range := by
    intro g k hgk
    have hmemI : (g : MulAut R) ∈ I := (hJmem _).mp g.2
    have hpelt : GGL45IsPElt p (g : MulAut R) := ⟨k, by
      have := congrArg Subtype.val hgk
      simpa using this⟩
    obtain ⟨r, hr⟩ := hG1 (g : MulAut R) hmemI hpelt
    exact ⟨r, Subtype.ext hr.symm⟩
  obtain ⟨u₀, hu₀I, f₀, hf₀, huf⟩ := hAI α₀ hα₀
  let ᾱ₀ : MulAut R := kgInducedAut θ α₀
  have hᾱ₀p : ᾱ₀ ^ p = 1 := by
    rw [show ᾱ₀ = kgInducedAut θ α₀ from rfl, ← map_pow, hA.2 α₀ hα₀, map_one]
  have hnotI : u₀ * f₀ ∉ I := by rw [← huf]; exact hα₀I
  have hxp : (u₀ * f₀) ^ p = 1 := by
    rw [← huf, ← map_pow, hA.2 α₀ hα₀, map_one]
  obtain ⟨u', hu'I, f', hf'F, hord, heq⟩ :=
    kgLangFieldConj_root hconj hs hna hu₀I hf₀ hnotI hxp
  have hᾱ₀eq : ᾱ₀ = u' * f' * u'⁻¹ := huf.trans heq
  have hᾱ₀closure : ᾱ₀ ∈ Subgroup.closure (I ∪ F) := by
    rw [show ᾱ₀ = u₀ * f₀ from huf]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hu₀I))
      (Subgroup.closure_mono (Set.subset_union_right) hf₀)
  have hᾱ₀S : ᾱ₀ ∈ S := hS ᾱ₀ hᾱ₀closure ⟨1, by rw [pow_one, hᾱ₀p]⟩
  let F₁ : MulAut R →* MulAut R := (MulAut.conj ᾱ₀).toMonoidHom
  have hstabβ : ∀ g ∈ J, F₁ g ∈ J := by
    intro g hg
    change MulAut.conj ᾱ₀ g ∈ J
    rw [MulAut.conj_apply]
    exact (Subgroup.normal_subgroupOf_iff hJS).mp hJn g ᾱ₀ hg hᾱ₀S
  obtain ⟨β, hβ⟩ := kgLang_exists_mulAut_restrict F₁ hstabβ
    (fun x _ y _ hxy => (MulAut.conj ᾱ₀).injective hxy)
  have hβι : ∀ r, ι (kgInducedAut θ α₀ r) = β (ι r) := by
    intro r
    apply Subtype.ext
    rw [hβ]
    change MulAut.conj (ᾱ₀ r) = MulAut.conj ᾱ₀ (ι r)
    rw [MulAut.conj_apply]
    exact kgLangInnerAux_conj_mul_apply ᾱ₀ r
  let A₀ : Subgroup (MulAut (HopfCover R)) :=
    A ⊓ Subgroup.comap (kgInducedAut θ) J
  have hA₀elem : IsElemAbelian p A₀ := kgLangInnerAux_isElemAbelian_of_le hA inf_le_left
  let Ā : Subgroup (MulAut R) := Subgroup.map (kgInducedAut θ) A₀
  have hĀelem : IsElemAbelian p Ā := kgLangInnerAux_isElemAbelian_map (kgInducedAut θ) hA₀elem
  have hĀJ : Ā ≤ J := by
    rintro a ⟨α, hα, rfl⟩
    exact hα.2
  have hᾱ₀conj : ∀ a ∈ Ā, F₁ a = a := by
    rintro a ⟨α, hα, rfl⟩
    have hcommA : α₀ * α = α * α₀ := by
      letI : IsMulCommutative A := hA.1
      exact congrArg (fun x : A => (x : MulAut (HopfCover R)))
        (mul_comm' (⟨α₀, hα₀⟩ : A) (⟨α, hα.1⟩ : A))
    change MulAut.conj ᾱ₀ (kgInducedAut θ α) = kgInducedAut θ α
    rw [MulAut.conj_apply]
    have h2 := congrArg (kgInducedAut θ) hcommA
    rw [map_mul, map_mul] at h2
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  have hu'J : u' ∈ J := (hJmem u').mpr hu'I
  let G₁ : MulAut R →* MulAut R := (MulAut.conj u').toMonoidHom
  let G₁inv : MulAut R →* MulAut R := (MulAut.conj u'⁻¹).toMonoidHom
  let F₁' : MulAut R →* MulAut R := (MulAut.conj f').toMonoidHom
  have hf'eq : f' = u'⁻¹ * ᾱ₀ * u' := by
    calc f' = u'⁻¹ * (u' * f' * u'⁻¹) * u' := by group
      _ = u'⁻¹ * ᾱ₀ * u' := by rw [← hᾱ₀eq]
  have hF₁_conj : ∀ y : MulAut R, F₁ (G₁ y) = G₁ (F₁' y) := by
    intro y
    change MulAut.conj ᾱ₀ (MulAut.conj u' y) = MulAut.conj u' (MulAut.conj f' y)
    rw [hᾱ₀eq, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hF₁'_conj : ∀ y : MulAut R, F₁' (G₁inv y) = G₁inv (F₁ y) := by
    intro y
    change MulAut.conj f' (MulAut.conj u'⁻¹ y) = MulAut.conj u'⁻¹ (MulAut.conj ᾱ₀ y)
    rw [hf'eq, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hendpow : ∀ (i : ℕ) (y : MulAut R),
      endPow F₁ i (G₁ y) = G₁ (endPow F₁' i y) := by
    intro i
    induction i with
    | zero => intro y; simp [endPow_apply]
    | succ i ih =>
        intro y
        rw [kgLangInnerAux_endPow_succ, ih y, hF₁_conj, ← kgLangInnerAux_endPow_succ]
  let E' : Subgroup (MulAut R) := Subgroup.map G₁inv Ā
  have hE'elem : IsElemAbelian p E' := kgLangInnerAux_isElemAbelian_map G₁inv hĀelem
  have hE'J : E' ≤ J := by
    rintro x ⟨a, ha, rfl⟩
    change MulAut.conj u'⁻¹ a ∈ J
    rw [MulAut.conj_apply]
    exact J.mul_mem (J.mul_mem (J.inv_mem hu'J) (hĀJ ha)) hu'J
  have hE'fix : ∀ x ∈ E', F₁' x = x := by
    rintro x ⟨a, ha, rfl⟩
    show F₁' (G₁inv a) = G₁inv a
    rw [hF₁'_conj a, hᾱ₀conj a ha]
  obtain ⟨N', hN'J, hN'ab, hN'stab, hN'90, hE'N'⟩ :=
    hT J hJI f' hf'F hord E' hE'elem (fun x hx => ⟨hE'J hx, hE'fix x hx⟩)
  let N₀ : Subgroup (MulAut R) := Subgroup.map G₁ N'
  have hN₀J : N₀ ≤ J := by
    rintro x ⟨y, hy, rfl⟩
    change MulAut.conj u' y ∈ J
    rw [MulAut.conj_apply]
    exact J.mul_mem (J.mul_mem hu'J (hN'J hy)) (J.inv_mem hu'J)
  have hN₀ab : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
    change MulAut.conj u' a' * MulAut.conj u' b' = MulAut.conj u' b' * MulAut.conj u' a'
    rw [← map_mul, ← map_mul, hN'ab a' ha' b' hb']
  have hN₀stab : ∀ x ∈ N₀, F₁ x ∈ N₀ := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨F₁' y, hN'stab y hy, (hF₁_conj y).symm⟩
  have hN₀90 : ∀ c ∈ N₀, ((List.range p).map fun i => endPow F₁ i c).prod = 1 →
      ∃ s ∈ N₀, c = s⁻¹ * F₁ s := by
    rintro c ⟨c', hc', rfl⟩ hprod
    have hmap : List.map (fun i => endPow F₁ i (G₁ c')) (List.range p)
        = List.map G₁ (List.map (fun i => endPow F₁' i c') (List.range p)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hendpow i c'
    have hprod' : ((List.range p).map fun i => endPow F₁' i c').prod = 1 := by
      apply (MulAut.conj u').injective
      rw [map_one]
      change G₁ ((List.range p).map fun i => endPow F₁' i c').prod = 1
      have hmp : G₁ ((List.range p).map fun i => endPow F₁' i c').prod
          = (List.map G₁ (List.map (fun i => endPow F₁' i c') (List.range p))).prod :=
        MonoidHom.map_list_prod G₁ _
      rw [hmp, ← hmap]
      exact hprod
    obtain ⟨s', hs'N', hs'⟩ := hN'90 c' hc' hprod'
    refine ⟨G₁ s', Subgroup.mem_map.mpr ⟨s', hs'N', rfl⟩, ?_⟩
    rw [hs']
    show G₁ (s'⁻¹ * F₁' s') = (G₁ s')⁻¹ * F₁ (G₁ s')
    rw [map_mul, map_inv, hF₁_conj s']
  have hĀN₀ : Ā ≤ N₀ := by
    intro a ha
    have hxa : G₁inv a ∈ E' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have h1 : G₁inv a ∈ N' := hE'N' hxa
    have h2 : G₁ (G₁inv a) ∈ N₀ := Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    rwa [show G₁ (G₁inv a) = a by
      change MulAut.conj u' (MulAut.conj u'⁻¹ a) = a
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group] at h2
  have hG6 : ∀ u ∈ J, ∃ g : ↥J, ∀ r, ι (u r) = g * ι r * g⁻¹ := by
    intro u hu
    refine ⟨⟨u, hu⟩, fun r => ?_⟩
    apply Subtype.ext
    show MulAut.conj (u r) = u * (ι r : MulAut R) * u⁻¹
    exact kgLangInnerAux_conj_mul_apply u r
  have hG5 : ∀ g : ↥J, (∀ r, g * ι r = ι r * g) → g = 1 := by
    intro g hg
    have hfix : ∀ r, (g : MulAut R) r = r := by
      intro r
      have hcommg : (g : MulAut R) * MulAut.conj r = MulAut.conj r * (g : MulAut R) := by
        have := congrArg Subtype.val (hg r)
        simpa [ι] using this
      have h1 : MulAut.conj ((g : MulAut R) r) = MulAut.conj r := by
        rw [kgLangInnerAux_conj_mul_apply]
        rw [hcommg, mul_assoc, mul_inv_cancel, mul_one]
      exact hconj_inj h1
    apply Subtype.ext
    ext r
    simpa using hfix r
  obtain ⟨h, hh1, hh2, hh3⟩ := kgLangModelHom θ hcomm ι hι hG5 J hG6 A hA α₀ hα₀ β hβι
  have hmeq : ∀ α ∈ A, ∀ (hαJ : kgInducedAut θ α ∈ J), kgInducedAut θ α ∈ I →
      h α = ⟨kgInducedAut θ α, hαJ⟩ := by
    intro α hα hαJ hαI
    exact kgLangInnerAux_eq_of_conj ι hG5 (hh1 α hα hαJ).2.2 (fun r => by
      apply Subtype.ext
      show MulAut.conj (kgInducedAut θ α r) =
        kgInducedAut θ α * (ι r : MulAut R) * (kgInducedAut θ α)⁻¹
      exact kgLangInnerAux_conj_mul_apply (kgInducedAut θ α) r)
  let N : Subgroup ↥J := N₀.subgroupOf J
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hN₀ab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
  have hβstabN : ∀ x ∈ N, β x ∈ N := by
    intro x hx
    have hx₀ : (x : MulAut R) ∈ N₀ := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_subgroupOf, hβ x]
    exact hN₀stab x hx₀
  have hβN : ∀ g : ↥J, β g ∈ N ↔ g ∈ N := kgLang_mulAut_mem_iff β hβstabN
  have hH90 : ∀ c ∈ N, ((List.range p).map fun i => (β ^ i) c).prod = 1 →
      ∃ s ∈ N, c = s⁻¹ * β s := by
    intro c hc hprod
    have hc₀ : (c : MulAut R) ∈ N₀ := Subgroup.mem_subgroupOf.mp hc
    have hprod₀ : ((List.range p).map fun i => endPow F₁ i (c : MulAut R)).prod = 1 := by
      have h := congrArg (Subgroup.subtype J) hprod
      rw [map_list_prod, map_one] at h
      have hlist : List.map (Subgroup.subtype J) (List.map (fun i => (β ^ i) c) (List.range p))
          = List.map (fun i => endPow F₁ i (c : MulAut R)) (List.range p) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        rw [Function.comp_apply, Subgroup.subtype_apply]
        exact kgLang_mulAut_pow_coe β F₁ hβ i c
      rwa [hlist] at h
    obtain ⟨s, hsN₀, hs⟩ := hN₀90 c hc₀ hprod₀
    refine ⟨⟨s, hN₀J hsN₀⟩, Subgroup.mem_subgroupOf.mpr hsN₀, ?_⟩
    apply Subtype.ext
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, hβ]
  have hh : ∀ α ∈ A, kgInducedAut θ α ∈ I → h α ∈ N ∧ h α ^ p = 1 ∧ β (h α) = h α ∧
      ∀ r, ι (kgInducedAut θ α r) = h α * ι r * (h α)⁻¹ := by
    intro α hα hαI
    have hαJ : kgInducedAut θ α ∈ J := (hJmem _).mpr hαI
    have hαĀ : kgInducedAut θ α ∈ Ā := by
      refine Subgroup.mem_map.mpr ⟨α, Subgroup.mem_inf.mpr ⟨hα, ?_⟩, rfl⟩
      exact (hJmem _).mpr hαI
    have hspec := hh1 α hα hαJ
    refine ⟨?_, hspec.1, hspec.2.1, hspec.2.2⟩
    rw [hmeq α hα hαJ hαI]
    exact Subgroup.mem_subgroupOf.mpr (hĀN₀ hαĀ)
  obtain ⟨α₁, hα₁A, hα₁ne, hα₁I⟩ := hA0
  have hne : ∃ α ∈ A, kgInducedAut θ α ∈ I ∧ h α ≠ 1 :=
    ⟨α₁, hα₁A, hα₁I, hh2 α₁ hα₁A ((hJmem _).mpr hα₁I) hα₁ne⟩
  obtain ⟨M, hMab, hMst, hMfix, hM90, e, heM, he1, hep, heα₀, -⟩ :=
    kgLangLT5_of_model hp θ (hZ θ hcomm) I A α₀ ι hι hG1' β hβι N hNab hβN hH90 h hh hne
  exact ⟨M, hMab, hMst, hMfix, hM90, e, heM, he1, hep, heα₀⟩

end CFSG.StandardType
