module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
public import CFSG.LocalAnalysis.StandardType.GGSharedInvolution
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

theorem GGFixLineComp.eq_of_fix_iff [Finite G] {Bs P Q : Subgroup G} {u v : G}
    (hP : GGFixLineComp Bs u P) (hQ : GGFixLineComp Bs v Q)
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1) (hBP : Bs ≤ Subgroup.normalizer (P : Set G))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer P Bs, φ b = b) ↔ ∀ φ ∈ ggAutomizer Q Bs, φ b = b)
    {r : MulAut ↥Bs} (hrP : r ∈ ggAutomizer P Bs) (hrQ : r ∈ ggAutomizer Q Bs) (hr2 : r ^ 2 = 1)
    (hr1 : r ≠ 1) : P = Q := by
  have hu_mem : (u : G) ∈ Subgroup.zpowers v := by
    have h1 : ∀ φ ∈ ggAutomizer P Bs, φ ⟨u, hP.mem⟩ = ⟨u, hP.mem⟩ :=
      (hP.fix_iff ⟨u, hP.mem⟩).2 (Subgroup.mem_zpowers u)
    have h2 : ∀ φ ∈ ggAutomizer Q Bs, φ ⟨u, hP.mem⟩ = ⟨u, hP.mem⟩ :=
      (hfix ⟨u, hP.mem⟩).1 h1
    exact (hQ.fix_iff ⟨u, hP.mem⟩).1 h2
  have hv_mem : (v : G) ∈ Subgroup.zpowers u := by
    have h1 : ∀ φ ∈ ggAutomizer Q Bs, φ ⟨v, hQ.mem⟩ = ⟨v, hQ.mem⟩ :=
      (hQ.fix_iff ⟨v, hQ.mem⟩).2 (Subgroup.mem_zpowers v)
    have h2 : ∀ φ ∈ ggAutomizer P Bs, φ ⟨v, hQ.mem⟩ = ⟨v, hQ.mem⟩ :=
      (hfix ⟨v, hQ.mem⟩).2 h1
    exact (hP.fix_iff ⟨v, hQ.mem⟩).1 h2
  have hzp : Subgroup.zpowers u = Subgroup.zpowers v :=
    le_antisymm (Subgroup.zpowers_le.mpr hu_mem) (Subgroup.zpowers_le.mpr hv_mem)
  have hcent_u : Subgroup.centralizer ({u} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    rw [Subgroup.zpowers_eq_closure u, Subgroup.centralizer_closure]
  have hcent_v : Subgroup.centralizer ({v} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers v : Set G) := by
    rw [Subgroup.zpowers_eq_closure v, Subgroup.centralizer_closure]
  have hcent : Subgroup.centralizer ({u} : Set G) = Subgroup.centralizer ({v} : Set G) := by
    rw [hcent_u, hcent_v, hzp]
  have hQ' : IsComponentOf Q (Subgroup.centralizer ({u} : Set G)) := by
    simpa only [hcent] using hQ.isComponentOf
  exact eq_of_isComponentOf_of_mem_ggAutomizer hP.isComponentOf hQ' hBs hBP hrP hrQ hr2 hr1

theorem GGFixLineComp.eq_of_map_congr [Finite G] {Bs P Q : Subgroup G} {u v : G}
    (hP : GGFixLineComp Bs u P) (hQ : GGFixLineComp Bs v Q)
    (hBs : ∀ b ∈ Bs, b * b = 1 → b = 1) (hBP : Bs ≤ Subgroup.normalizer (P : Set G))
    {V : Type*} [Group V] (eta : ↥Bs ≃* V)
    (hfix : ∀ f : V, (∀ w ∈ (ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom, w f = f) ↔
      ∀ w ∈ (ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom, w f = f)
    {τ : MulAut V} (hτP : τ ∈ (ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom)
    (hτQ : τ ∈ (ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom) (hτ2 : τ ^ 2 = 1)
    (hτ1 : τ ≠ 1) : P = Q := by
  let r : MulAut ↥Bs := (MulAut.congr eta).symm τ
  have hrP : r ∈ ggAutomizer P Bs := by
    obtain ⟨ψ, hψ, hψτ⟩ := Subgroup.mem_map.mp hτP
    have : r = ψ := by
      dsimp only [r]
      rw [← hψτ]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rwa [this]
  have hrQ : r ∈ ggAutomizer Q Bs := by
    obtain ⟨ψ, hψ, hψτ⟩ := Subgroup.mem_map.mp hτQ
    have : r = ψ := by
      dsimp only [r]
      rw [← hψτ]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rwa [this]
  have hr2 : r ^ 2 = 1 := by
    have h := congrArg (fun x => (MulAut.congr eta).symm x) hτ2
    simpa only [r, map_pow, map_one] using h
  have hr1 : r ≠ 1 := by
    intro h
    apply hτ1
    calc τ = MulAut.congr eta r := (MulEquiv.apply_symm_apply (MulAut.congr eta) τ).symm
      _ = MulAut.congr eta 1 := by rw [h]
      _ = 1 := map_one _
  have hfix' : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer P Bs, φ b = b) ↔
      ∀ φ ∈ ggAutomizer Q Bs, φ b = b := by
    intro b
    rw [← CFSG.StandardType.forall_map_congr_fix_iff eta (ggAutomizer P Bs) b,
      ← CFSG.StandardType.forall_map_congr_fix_iff eta (ggAutomizer Q Bs) b]
    exact hfix (eta b)
  exact GGFixLineComp.eq_of_fix_iff hP hQ hBs hBP hfix' hrP hrQ hr2 hr1

theorem exists_mem_of_mem_map_congr {Bs W : Subgroup G} {V : Type*} [Group V]
    (eta : ↥Bs ≃* V) {s : MulAut V}
    (hs : s ∈ (ggAutomizer W Bs).map (MulAut.congr eta).toMonoidHom) :
    ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)), g ∈ W ∧
      MulAut.congr eta (ggConjAut Bs hg) = s := by
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hs
  rw [ggAutomizer_eq] at hφ
  obtain ⟨g, hgW, hgN, hgφ⟩ := hφ
  refine ⟨g, hgN, hgW, ?_⟩
  have hφeq : ggConjAut Bs hgN = φ := by
    ext b
    rw [ggConjAut_apply, hgφ b]
  rw [hφeq]
  rfl

theorem map_conj_le_sup {W X : Subgroup G} {g : G} (hg : g ∈ W) :
    X.map (MulAut.conj g).toMonoidHom ≤ W ⊔ X := by
  rintro y ⟨x, hx, rfl⟩
  change MulAut.conj g x ∈ W ⊔ X
  rw [MulAut.conj_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
    (Subgroup.mem_sup_right hx)) (Subgroup.mem_sup_left (Subgroup.inv_mem W hg))

theorem GGNbr.mem_closure_pair [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G}
    {y y₀ : G} {K K₀ : Subgroup G} (hn : GGNbr p B x D J y K) (hn₀ : GGNbr p B x D J y₀ K₀) :
    y ∈ Subgroup.closure ({x, y₀} : Set G) := by
  have hy : y ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [← hn.2.1, hn₀.2.1] at hy
  exact hy

theorem GGConfig.not_mem_zpowers_of_ggNbr [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J)
    (hn : GGNbr p B x D J y K) : y ∉ Subgroup.zpowers x := by
  intro hy
  have hcardD : Nat.card D = p ^ 2 := hc.2.2.1.2.2.1
  have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hzx | hzy
      · rw [hzx]
        exact Subgroup.mem_zpowers x
      · rw [hzy]
        exact hy
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hD : D = Subgroup.zpowers x := by
    rw [hn.2.1, hcl]
  have hcard : p ^ 2 = p := by
    rw [← hcardD, hD, Nat.card_zpowers, hc.orderOf_x]
  have hp2 : 2 ≤ p := hc.tableB_facts.1.two_le
  have hpp : p * p = p := by simpa [pow_two] using hcard
  nlinarith

theorem mem_closure_pair_map {Bs : Subgroup G} {V : Type*} [Group V] (eta : ↥Bs ≃* V)
    {x y y₀ : ↥Bs} (h : (y : G) ∈ Subgroup.closure ({(x : G), (y₀ : G)} : Set G)) :
    eta y ∈ Subgroup.closure {eta x, eta y₀} := by
  have h1 : y ∈ Subgroup.closure ({x, y₀} : Set ↥Bs) := by
    have hmap : Subgroup.closure ({(x : G), (y₀ : G)} : Set G) =
        (Subgroup.closure ({x, y₀} : Set ↥Bs)).map (Subgroup.subtype Bs) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp only [Subgroup.coe_subtype]
    rw [hmap, Subgroup.mem_map] at h
    obtain ⟨w, hw, hw_eq⟩ := h
    have hwy : w = y := Subgroup.subtype_injective Bs hw_eq
    rwa [hwy] at hw
  have h2 := MonoidHom.map_closure eta.toMonoidHom ({x, y₀} : Set ↥Bs)
  rw [Set.image_pair] at h2
  simp only [MulEquiv.coe_toMonoidHom] at h2 ⊢
  rw [← h2]
  exact ⟨y, h1, rfl⟩

theorem not_mem_zpowers_map {Bs : Subgroup G} {V : Type*} [Group V] (eta : ↥Bs ≃* V)
    {x y : ↥Bs} (h : (y : G) ∉ Subgroup.zpowers (x : G)) :
    eta y ∉ Subgroup.zpowers (eta x) := by
  intro hmem
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  apply h
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  have hk' : eta y = eta (x ^ k) := by
    rw [map_zpow, hk]
  have hxy : y = x ^ k := eta.injective hk'
  rw [hxy]
  simp

end CFSG.StandardType

end
