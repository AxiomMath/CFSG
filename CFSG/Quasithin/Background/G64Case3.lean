module

public import CFSG.Quasithin.Background.G64Case3Piece
public import CFSG.Quasithin.Background.G64ProofGroup

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

section Conj

variable {M : Type*} [Group M]

theorem mem_map_conj {H : Subgroup M} {g x : M} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem map_conj_mul (H : Subgroup M) (g h : M) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (H : Subgroup M) : H.map (MulAut.conj (1 : M)).toMonoidHom = H := by
  ext x
  rw [mem_map_conj]
  simp

theorem map_conj_le {H L : Subgroup M} {g : M} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ L) :
    H.map (MulAut.conj g).toMonoidHom ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem card_map_conj [Finite M] (H : Subgroup M) (g : M) :
    Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem le_of_map_conj_le {H L : Subgroup M} {g : M}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom) : H ≤ L := by
  intro x hx
  have := h ⟨x, hx, rfl⟩
  rw [mem_map_conj] at this
  simpa [mul_assoc] using this

end Conj

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {a : MulAut V}

theorem map_conj_le_or [Finite V] {G₁ G₂ : Subgroup (MulAut V)} {W₂ : Subgroup V}
    (hW : commV G₁ ⊔ W₂ = ⊤) (hfix₁₂ : ∀ g ∈ G₁, ∀ w ∈ W₂, g w = w)
    (hirr : ∀ Y : Subgroup V, Y ≤ commV G₁ → (∀ g ∈ G₁, ∀ y ∈ Y, g y ∈ Y) → Y ≠ ⊥ →
      Y = commV G₁)
    {D : Set (MulAut V)} (hDtr : ∀ d ∈ D, Nat.card (commV (Subgroup.zpowers d)) = 2)
    (hD12 : ∀ d ∈ D, d ∈ G₁ ∨ d ∈ G₂) (hcomm : ∀ x ∈ G₁, ∀ y ∈ G₂, x * y = y * x)
    (hcl : Subgroup.closure {d | d ∈ D ∧ d ∈ G₁} = G₁) {g : MulAut V}
    (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    G₁.map (MulAut.conj g).toMonoidHom ≤ G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom ≤ G₂ := by
  classical
  have hmap : G₁.map (MulAut.conj g).toMonoidHom = Subgroup.closure
      ((MulAut.conj g).toMonoidHom '' {d | d ∈ D ∧ d ∈ G₁}) := by
    conv_lhs => rw [← hcl]
    exact MonoidHom.map_closure _ _
  by_cases h1 : ∀ d, d ∈ D → d ∈ G₁ → g * d * g⁻¹ ∈ G₁
  · left
    rw [hmap, Subgroup.closure_le]
    rintro _ ⟨d, ⟨hd, hd₁⟩, rfl⟩
    exact h1 d hd hd₁
  by_cases h2 : ∀ d, d ∈ D → d ∈ G₁ → g * d * g⁻¹ ∈ G₂
  · right
    rw [hmap, Subgroup.closure_le]
    rintro _ ⟨d, ⟨hd, hd₁⟩, rfl⟩
    exact h2 d hd hd₁
  exfalso
  push Not at h1 h2
  obtain ⟨e'', he''D, he''₁, he''⟩ := h1
  obtain ⟨e', he'D, he'₁, he'⟩ := h2
  have he''₂ : g * e'' * g⁻¹ ∈ G₂ := (hD12 _ (hgD _ he''D)).resolve_left he''
  have he'₁' : g * e' * g⁻¹ ∈ G₁ := (hD12 _ (hgD _ he'D)).resolve_right he'
  set E' : Set (MulAut V) := {d | d ∈ D ∧ d ∈ G₁ ∧ g * d * g⁻¹ ∈ G₁} with hE'
  set E'' : Set (MulAut V) := {d | d ∈ D ∧ d ∈ G₁ ∧ g * d * g⁻¹ ∈ G₂} with hE''
  have hcommE : ∀ x ∈ E', ∀ y ∈ E'', x * y = y * x := by
    rintro x ⟨-, -, hx⟩ y ⟨-, -, hy⟩
    have := hcomm _ hx _ hy
    have h3 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := this
        _ = g * (y * x) * g⁻¹ := by group
    simpa using h3
  set H' := Subgroup.closure E' with hH'
  set Y := commV H' with hY
  have hfixY : ∀ y ∈ E'', ∀ v ∈ Y, y v = v := by
    intro y hy v hv
    have hle : Y ≤ fixV (Subgroup.zpowers y) := by
      refine G6.commV_closure_le ?_
      intro x hx w
      rw [fixV_zpowers_iff]
      exact apply_eq_of_commute (hDtr x hx.1) (hcommE x hx y hy).symm
        (G6.mem_commV_of_mem (Subgroup.mem_zpowers x) w)
    exact fixV_zpowers_iff.1 (hle hv)
  have hYW : Y ≤ commV G₁ := G6.commV_mono ((Subgroup.closure_le _).2 fun x hx => hx.2.1)
  have hYinv : ∀ x ∈ G₁, ∀ y ∈ Y, x y ∈ Y := by
    have hle : G₁ ≤ invSub Y := by
      rw [← hcl, Subgroup.closure_le]
      rintro d ⟨hd, hd₁⟩
      rcases hD12 _ (hgD d hd) with h | h
      · intro y hy
        have hdH : d ∈ H' := Subgroup.subset_closure (show d ∈ E' from ⟨hd, hd₁, h⟩)
        exact G6.apply_mem_commV (fun x hx => H'.mul_mem (H'.mul_mem hdH hx) (H'.inv_mem hdH)) hy
      · intro y hy
        rw [hfixY d ⟨hd, hd₁, h⟩ y hy]
        exact hy
    exact fun x hx => hle hx
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have hle : commV (Subgroup.zpowers e') ≤ Y :=
      G6.commV_mono (Subgroup.zpowers_le.2
        (Subgroup.subset_closure (show e' ∈ E' from ⟨he'D, he'₁, he'₁'⟩)))
    rw [hbot, le_bot_iff] at hle
    have := hDtr e' he'D
    rw [hle, Subgroup.card_bot] at this
    omega
  have hYeq := hirr Y hYW hYinv hYne
  have he''1 : e'' = 1 := by
    ext v
    have hv : v ∈ commV G₁ ⊔ W₂ := by rw [hW]; trivial
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul, MulAut.one_apply, hfixY e'' ⟨he''D, he''₁, he''₂⟩ w₁ (hYeq ▸ hw₁),
      hfix₁₂ e'' he''₁ w₂ hw₂]
  have := hDtr e'' he''D
  rw [he''1] at this
  exact ne_one_of_card_two this rfl

theorem RedPiece.types {Gi : Subgroup (MulAut V)} (hp : RedPiece Gi (commV Gi) ⊥) :
    ModuleType Gi (commV Gi) ∧ FactorType Gi := by
  rcases hp with ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩
  · refine ⟨Or.inl ⟨2, le_rfl, by norm_num, ZMod 2, inferInstance, inferInstance, by simp,
      π, hπ⟩, Or.inl ⟨(MulEquiv.ofBijective π ⟨natSL_injective hπ, hπ.1⟩).symm⟩⟩
  · refine ⟨Or.inl ⟨3, by norm_num, by norm_num, ZMod 2, inferInstance, inferInstance, by simp,
      π, hπ⟩, Or.inr (Or.inl ⟨(MulEquiv.ofBijective π ⟨natSL_injective hπ, hπ.1⟩).symm⟩)⟩
  · refine ⟨Or.inr (Or.inl ⟨5, le_rfl, by norm_num, π, hπ⟩), Or.inr (Or.inr ⟨(MulEquiv.ofBijective
      π ⟨RealizesVia.injective_of_faithful' (symDn_faithful le_rfl) hπ, hπ.1⟩).symm⟩)⟩

theorem RedPiece.exists_eq_on [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Gi : Subgroup (MulAut V)}
    (hp : RedPiece Gi (commV Gi) ⊥) {d : MulAut V} (hd : d ∈ Gi)
    (htr : Nat.card (commV (Subgroup.zpowers d)) = 2) {g : MulAut V}
    (hg : ∀ x ∈ Gi, g * x * g⁻¹ ∈ Gi) : ∃ k ∈ Gi, ∀ w ∈ commV Gi, g w = k w := by
  have hgW : ∀ w ∈ commV Gi, g w ∈ commV Gi := fun w hw => G6.apply_mem_commV hg hw
  rcases hp with ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩
  · obtain ⟨k, hk, hkw⟩ := exists_eq_on_of_natSL hπ hgW
    exact ⟨k, hk, fun w hw => (hkw w hw).symm⟩
  · obtain ⟨k, hk, hkw⟩ := exists_eq_on_of_natSL hπ hgW
    exact ⟨k, hk, fun w hw => (hkw w hw).symm⟩
  · set π' : Perm (Fin 5) →* ↥Gi := π with hπ'def
    have hπ' : (FFModel.symDn 5).RealizesVia Gi (commV Gi) ⊥ π' := hπ
    have hinj : Function.Injective π' :=
      RealizesVia.injective_of_faithful' (symDn_faithful le_rfl) hπ'
    set θ : ↥Gi ≃* Perm (Fin 5) := (MulEquiv.ofBijective π' ⟨hinj, hπ'.1⟩).symm with hθ
    have hπθ : ∀ x : ↥Gi, π' (θ x) = x := fun x =>
      (MulEquiv.ofBijective π' ⟨hinj, hπ'.1⟩).apply_symm_apply x
    have hswap : ∀ (x : MulAut V) (hx : x ∈ Gi), Nat.card (commV (Subgroup.zpowers x)) = 2 →
        (θ ⟨x, hx⟩).IsSwap := by
      intro x hx hxt
      refine isSwap_of_symNat hV2 le_rfl hπ' ?_
      rw [hπθ]
      exact hxt
    have htr' := card_swapAut_of_isSwap θ hd (hswap d hd htr) htr
    have htrσ : ∀ σ : Perm (Fin 5), σ.IsSwap →
        Nat.card (commV (Subgroup.zpowers ((θ.symm σ : ↥Gi) : MulAut V))) = 2 := by
      rintro σ ⟨i, j, hij, rfl⟩
      exact htr' i j hij
    exact exists_eq_on_of_normalizes (by norm_num) θ htrσ hswap hg

theorem statedSL_ne_bot {n : ℕ} (hn : 2 ≤ n) (F : Type) [Field F] :
    ∃ x : ↥(StatedSL n F), x ≠ 1 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨⟨Matrix.GeneralLinearGroup.transvection _ _ h01 1, Subgroup.subset_closure
    (Matrix.det_transvection_of_ne _ _ h01 1)⟩, fun h => ?_⟩
  have := congrArg (fun x : ↥(StatedSL n F) =>
    ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ⟨0, by omega⟩ ⟨1, by omega⟩) h
  simp [Matrix.transvection, h01] at this

theorem ne_bot_of_factorList {Gi : Subgroup (MulAut V)} (hf : B56FactorList ↥Gi) : Gi ≠ ⊥ := by
  intro hbot
  have hsub : ∀ x y : ↥Gi, x = y := fun x y => by
    apply Subtype.ext
    have hx : (x : MulAut V) ∈ (⊥ : Subgroup (MulAut V)) := hbot ▸ x.2
    have hy : (y : MulAut V) ∈ (⊥ : Subgroup (MulAut V)) := hbot ▸ y.2
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  rcases hf with ⟨n, F, _, _, -, -, ⟨e⟩⟩ | h5 | ⟨m, F, _, _, -, -, -, ⟨e⟩⟩
  · obtain ⟨x, hx⟩ := statedSL_ne_bot (n := 2) le_rfl F
    exact hx (e.symm.injective (hsub _ _))
  · obtain ⟨e⟩ := h5
    have : swap (0 : Fin 5) 1 = 1 := e.symm.injective (hsub _ _)
    have := congrArg (fun σ : Perm (Fin 5) => σ 0) this
    simp at this
  · obtain ⟨x, hx⟩ := statedSL_ne_bot (n := 3) (by norm_num) F
    exact hx (e.symm.injective (hsub _ _))

theorem commV_sup_le (G₁ G₂ : Subgroup (MulAut V)) :
    commV (G₁ ⊔ G₂) ≤ commV G₁ ⊔ commV G₂ :=
  CFSG.Quasithin.FixVLat.commV_sup_le G₁ G₂

theorem case3_split [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    (hC : B56Case3 (conjClosure (Subgroup.zpowers a) G)) :
    ∃ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = conjClosure (Subgroup.zpowers a) G ∧
      G₁ ⊓ G₂ = ⊥ ∧ (∀ x ∈ G₁, ∀ y ∈ G₂, x * y = y * x) ∧ commV G₁ ⊔ commV G₂ = ⊤ ∧
      (∀ g ∈ G₁, ∀ w ∈ commV G₂, g w = w) ∧ (∀ g ∈ G₂, ∀ w ∈ commV G₁, g w = w) ∧
      RedPiece G₁ (commV G₁) ⊥ ∧ RedPiece G₂ (commV G₂) ⊥ ∧
      (∀ d ∈ transSet G a, d ∈ G₁ ∨ d ∈ G₂) ∧ (∃ d ∈ transSet G a, d ∈ G₁) ∧
      (∃ d ∈ transSet G a, d ∈ G₂) := by
  classical
  set K := conjClosure (Subgroup.zpowers a) G with hKdef
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hf₁, hf₂, W₁, W₂, hCW₁, hCW₂, hinv₁, hinv₂, hW, hWinf,
    hp₁, hp₂⟩ := hC
  set C := fixV K with hCdef
  set D := transSet G a with hD
  have hKV : commV K = ⊤ := commV_classK h
  have hDK : Subgroup.closure D = K := closure_transSet G a
  have hG₁K : G₁ ≤ K := hsup ▸ le_sup_left
  have hG₂K : G₂ ≤ K := hsup ▸ le_sup_right
  have hKinv₁ : ∀ k ∈ K, ∀ w ∈ W₁, k w ∈ W₁ := fun k hk w hw => hinv₁ ⟨k, hk⟩ w hw
  have hKinv₂ : ∀ k ∈ K, ∀ w ∈ W₂, k w ∈ W₂ := fun k hk w hw => hinv₂ ⟨k, hk⟩ w hw
  have hinv₁' : ∀ g ∈ G₁, ∀ w ∈ W₁, g w ∈ W₁ := fun g hg => hKinv₁ g (hG₁K hg)
  have hinv₂' : ∀ g ∈ G₂, ∀ w ∈ W₂, g w ∈ W₂ := fun g hg => hKinv₂ g (hG₂K hg)
  have hcV₁ : commV G₁ ≤ W₁ := B56Piece.commV_le hp₁
  have hcV₂ : commV G₂ ≤ W₂ := B56Piece.commV_le hp₂
  have htriv₁₂ : ∀ g ∈ G₁, ∀ w ∈ W₂, g w * w⁻¹ ∈ C := by
    intro g hg w hw
    rw [← hWinf]
    exact ⟨hcV₁ (G6.mem_commV_of_mem hg w),
      W₂.mul_mem (hKinv₂ g (hG₁K hg) w hw) (W₂.inv_mem hw)⟩
  have htriv₂₁ : ∀ g ∈ G₂, ∀ w ∈ W₁, g w * w⁻¹ ∈ C := by
    intro g hg w hw
    rw [← hWinf]
    exact ⟨W₁.mul_mem (hKinv₁ g (hG₂K hg) w hw) (W₁.inv_mem hw),
      hcV₂ (G6.mem_commV_of_mem hg w)⟩
  have hCfix : ∀ k ∈ K, ∀ c ∈ C, k c = c := fun k hk c hc => (mem_fixV.1 hc) k hk
  have hfaith₁ : ∀ {g : MulAut V}, g ∈ G₁ → (∀ w ∈ W₁, g w * w⁻¹ ∈ C) → g = 1 :=
    fun hg ht => B56Piece.faithful hp₁ hinv₁' hCW₁ hg ht
  have hfaith₂ : ∀ {g : MulAut V}, g ∈ G₂ → (∀ w ∈ W₂, g w * w⁻¹ ∈ C) → g = 1 :=
    fun hg ht => B56Piece.faithful hp₂ hinv₂' hCW₂ hg ht
  have h12n : G₁ ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := le_normalizer_of_commute hcomm
  have hDsplit : ∀ d ∈ D, d ∈ G₁ ∨ d ∈ G₂ := by
    intro d hd
    have hdK : d ∈ K := transSet_subset G a hd
    have hdtr := card_commV_conj htr hd
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := mem_sup_of_normalizer h12n (hsup ▸ hdK)
    by_cases hm₁ : ∃ w ∈ W₁, (g₁ * g₂) w * w⁻¹ ∉ C
    · by_cases hm₂ : ∃ w ∈ W₂, (g₁ * g₂) w * w⁻¹ ∉ C
      · exfalso
        obtain ⟨w₁, hw₁, hm₁⟩ := hm₁
        obtain ⟨w₂, hw₂, hm₂⟩ := hm₂
        exact false_of_two_moved hdtr (fun u hu => hKinv₁ _ hdK u hu)
          (fun u hu => hKinv₂ _ hdK u hu) hWinf.le hw₁ hw₂ hm₁ hm₂
      · push Not at hm₂
        left
        have : g₂ = 1 := by
          refine hfaith₂ hg₂ fun w hw => ?_
          have h1 := hm₂ w hw
          have h2 := htriv₁₂ g₁⁻¹ (G₁.inv_mem hg₁) w hw
          have h3 : g₁⁻¹ ((g₁ * g₂) w * w⁻¹) = (g₁ * g₂) w * w⁻¹ :=
            hCfix _ (K.inv_mem (hG₁K hg₁)) _ h1
          have h4 : g₂ w * w⁻¹ = g₁⁻¹ ((g₁ * g₂) w * w⁻¹) * (g₁⁻¹ w * w⁻¹) := by
            simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
              MulEquiv.symm_apply_apply]
            group
          rw [h4, h3]
          exact C.mul_mem h1 h2
        rw [this, mul_one]
        exact hg₁
    · push Not at hm₁
      right
      have hc : g₁ * g₂ = g₂ * g₁ := hcomm g₁ hg₁ g₂ hg₂
      have : g₁ = 1 := by
        refine hfaith₁ hg₁ fun w hw => ?_
        have h1 := hm₁ w hw
        rw [hc] at h1
        have h2 := htriv₂₁ g₂⁻¹ (G₂.inv_mem hg₂) w hw
        have h3 : g₂⁻¹ ((g₂ * g₁) w * w⁻¹) = (g₂ * g₁) w * w⁻¹ :=
          hCfix _ (K.inv_mem (hG₂K hg₂)) _ h1
        have h4 : g₁ w * w⁻¹ = g₂⁻¹ ((g₂ * g₁) w * w⁻¹) * (g₂⁻¹ w * w⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
            MulEquiv.symm_apply_apply]
          group
        rw [h4, h3]
        exact C.mul_mem h1 h2
      rw [this, one_mul]
      exact hg₂
  have hcl₁ : Subgroup.closure {d | d ∈ D ∧ d ∈ G₁} = G₁ := by
    refine le_antisymm ((Subgroup.closure_le _).2 fun d hd => hd.2) fun x hx => ?_
    exact mem_closure_inter_of_mem hinf hcomm hDsplit (hDK ▸ hG₁K hx) hx
  have hcl₂ : Subgroup.closure {d | d ∈ D ∧ d ∈ G₂} = G₂ := by
    refine le_antisymm ((Subgroup.closure_le _).2 fun d hd => hd.2) fun x hx => ?_
    exact mem_closure_inter_of_mem (by rw [inf_comm]; exact hinf)
      (fun x hx y hy => (hcomm y hy x hx).symm) (fun d hd => (hDsplit d hd).symm)
      (hDK ▸ hG₂K hx) hx
  have hne : ∀ {Gi : Subgroup (MulAut V)},
      Subgroup.closure {d | d ∈ D ∧ d ∈ Gi} = Gi → Gi ≠ ⊥ → ∃ d ∈ D, d ∈ Gi := by
    intro Gi hcl hne
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← hcl, Subgroup.closure_eq_bot_iff]
    intro d hd
    exact absurd hd.2 (hcon d hd.1)
  obtain ⟨d₁, hd₁D, hd₁⟩ := hne hcl₁ (ne_bot_of_factorList hf₁)
  obtain ⟨d₂, hd₂D, hd₂⟩ := hne hcl₂ (ne_bot_of_factorList hf₂)
  have hd₁tr := card_commV_conj htr hd₁D
  have hd₂tr := card_commV_conj htr hd₂D
  have hVle : (⊤ : Subgroup V) ≤ commV G₁ ⊔ commV G₂ := by
    rw [← hKV, ← hsup]
    exact commV_sup_le G₁ G₂
  have hmc : ∀ {Gi Gj : Subgroup (MulAut V)} {Wi Wj : Subgroup V},
      Wi ⊔ Wj = ⊤ → Wi ⊓ Wj = C → C ≤ Wi → (∀ g ∈ Gi, ∀ w ∈ Wi, g w ∈ Wi) →
      (∀ g ∈ Gi, ∀ w ∈ Wj, g w * w⁻¹ ∈ C) → commV Gj ≤ Wj →
      (⊤ : Subgroup V) ≤ commV Gi ⊔ commV Gj → Wi ≤ modComm Gi Wi ⊔ C := by
    intro Gi Gj Wi Wj hWij hWinf' hCWi hinvi htrivij hcVj hVle'
    have hci : commV Gi ≤ modComm Gi Wi ⊔ C := by
      rw [G6.commV_le_iff]
      intro g hg v
      have hv : v ∈ Wi ⊔ Wj := by rw [hWij]; trivial
      obtain ⟨wi, hwi, wj, hwj, rfl⟩ := Subgroup.mem_sup.1 hv
      have : g (wi * wj) * (wi * wj)⁻¹ = (g wi * wi⁻¹) * (g wj * wj⁻¹) := by
        rw [map_mul, mul_inv, mul_mul_mul_comm]
      rw [this]
      refine Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨⟨g, hg⟩, wi, hwi, rfl⟩) ?_
      exact htrivij g hg wj hwj
    have hMW : modComm Gi Wi ⊔ C ≤ Wi := sup_le (modComm_le_of_inv hinvi) hCWi
    intro w hw
    have hw' : w ∈ (modComm Gi Wi ⊔ C) ⊔ Wj :=
      sup_le_sup hci hcVj (hVle' (Subgroup.mem_top w))
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw'
    have hyW : y ∈ Wi := by
      have : y = x⁻¹ * (x * y) := by group
      rw [this]
      exact Wi.mul_mem (Wi.inv_mem (hMW hx)) hw
    have hyC : y ∈ C := by rw [← hWinf']; exact ⟨hyW, hy⟩
    exact (modComm Gi Wi ⊔ C).mul_mem hx (Subgroup.mem_sup_right hyC)
  have hmc₁ := hmc hW hWinf hCW₁ hinv₁' htriv₁₂ hcV₂ hVle
  have hmc₂ := hmc (by rw [sup_comm]; exact hW) (by rw [inf_comm]; exact hWinf) hCW₂ hinv₂'
    htriv₂₁ hcV₁ (by rw [sup_comm]; exact hVle)
  have hd₁1 : d₁ ≠ 1 := ne_one_of_card_two hd₁tr
  have hd₂1 : d₂ ≠ 1 := ne_one_of_card_two hd₂tr
  obtain ⟨hW₁eq, hr₁⟩ := B56Piece.reduce hV2 hp₁ hmc₁ hd₁ hd₁1 hd₁tr
  obtain ⟨hW₂eq, hr₂⟩ := B56Piece.reduce hV2 hp₂ hmc₂ hd₂ hd₂1 hd₂tr
  have hC1 : C = ⊥ := by
    have hc₁ := RedPiece.card_commV_mul_le hV2 hr₁ hd₁ hd₁1 hd₁tr
    have hc₂ := RedPiece.card_commV_mul_le hV2 hr₂ hd₂ hd₂1 hd₂tr
    have hV : Nat.card V ≤ Nat.card (commV G₁) * Nat.card (commV G₂) := by
      rw [← Subgroup.card_top (G := V)]
      exact (Subgroup.card_le_of_le hVle).trans (card_sup_le _ _)
    have hWW := card_sup_mul_card_inf W₁ W₂
    rw [hW, hWinf, Subgroup.card_top] at hWW
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hVpos : 0 < Nat.card V := Nat.card_pos
    have key : Nat.card V * Nat.card C * Nat.card C ≤ Nat.card V * Nat.card C := by
      calc Nat.card V * Nat.card C * Nat.card C
          ≤ Nat.card (commV G₁) * Nat.card (commV G₂) * Nat.card C * Nat.card C :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hV)
        _ = (Nat.card (commV G₁) * Nat.card C) * (Nat.card (commV G₂) * Nat.card C) := by ring
        _ ≤ Nat.card W₁ * Nat.card W₂ := Nat.mul_le_mul hc₁ hc₂
        _ = Nat.card V * Nat.card C := hWW.symm
    have : Nat.card C ≤ 1 := by
      have h' : Nat.card V * Nat.card C * Nat.card C ≤ Nat.card V * Nat.card C * 1 := by
        rw [mul_one]; exact key
      exact Nat.le_of_mul_le_mul_left h' (by positivity)
    exact Subgroup.card_eq_one.1 (le_antisymm this hCpos)
  rw [hC1, sup_bot_eq] at hW₁eq hW₂eq
  rw [hC1, hW₁eq] at hr₁
  rw [hC1, hW₂eq] at hr₂
  refine ⟨G₁, G₂, hsup, hinf, hcomm, by rw [← hW₁eq, ← hW₂eq, hW], fun g hg w hw => ?_,
    fun g hg w hw => ?_, hr₁, hr₂, hDsplit, ⟨d₁, hd₁D, hd₁⟩, ⟨d₂, hd₂D, hd₂⟩⟩
  · have := htriv₁₂ g hg w (hW₂eq ▸ hw)
    rw [hC1, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this
  · have := htriv₂₁ g hg w (hW₁eq ▸ hw)
    rw [hC1, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this

theorem conclusion_of_split [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) {G₁ G₂ : Subgroup (MulAut V)}
    (hsup : G₁ ⊔ G₂ = conjClosure (Subgroup.zpowers a) G) (hinf : G₁ ⊓ G₂ = ⊥)
    (hcomm : ∀ x ∈ G₁, ∀ y ∈ G₂, x * y = y * x) (hW : commV G₁ ⊔ commV G₂ = ⊤)
    (hfix₁₂ : ∀ g ∈ G₁, ∀ w ∈ commV G₂, g w = w) (hfix₂₁ : ∀ g ∈ G₂, ∀ w ∈ commV G₁, g w = w)
    (hr₁ : RedPiece G₁ (commV G₁) ⊥) (hr₂ : RedPiece G₂ (commV G₂) ⊥)
    (hDsplit : ∀ d ∈ transSet G a, d ∈ G₁ ∨ d ∈ G₂) (hd₂ : ∃ d ∈ transSet G a, d ∈ G₂)
    (ha₁ : a ∈ G₁) : Conclusion G a := by
  classical
  set K := conjClosure (Subgroup.zpowers a) G with hKdef
  set D := transSet G a with hD
  have hDK : Subgroup.closure D = K := closure_transSet G a
  have hG₁K : G₁ ≤ K := hsup ▸ le_sup_left
  have hG₂K : G₂ ≤ K := hsup ▸ le_sup_right
  have hKG : K ≤ G := classK_le h
  have hDtr : ∀ d ∈ D, Nat.card (commV (Subgroup.zpowers d)) = 2 := fun d hd =>
    card_commV_conj htr hd
  have hgD : ∀ g ∈ G, ∀ d ∈ D, g * d * g⁻¹ ∈ D := fun g hg d hd => transSet_conj hg hd
  have hcomm' : ∀ x ∈ G₂, ∀ y ∈ G₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hcl₁ : Subgroup.closure {d | d ∈ D ∧ d ∈ G₁} = G₁ := by
    refine le_antisymm ((Subgroup.closure_le _).2 fun d hd => hd.2) fun x hx => ?_
    exact mem_closure_inter_of_mem hinf hcomm hDsplit (hDK ▸ hG₁K hx) hx
  have hcl₂ : Subgroup.closure {d | d ∈ D ∧ d ∈ G₂} = G₂ := by
    refine le_antisymm ((Subgroup.closure_le _).2 fun d hd => hd.2) fun x hx => ?_
    exact mem_closure_inter_of_mem (by rw [inf_comm]; exact hinf) hcomm'
      (fun d hd => (hDsplit d hd).symm) (hDK ▸ hG₂K hx) hx
  obtain ⟨d₂, hd₂D, hd₂⟩ := hd₂
  have hd₂tr := hDtr d₂ hd₂D
  have ha1 : a ≠ 1 := h.ne_one
  have hG₁ne : G₁ ≠ ⊥ := fun hb => ha1 (by rw [hb] at ha₁; exact Subgroup.mem_bot.1 ha₁)
  have hG₂ne : G₂ ≠ ⊥ := fun hb => ne_one_of_card_two hd₂tr
    (by rw [hb] at hd₂; exact Subgroup.mem_bot.1 hd₂)
  have hle₁ : ∀ g ∈ G, G₁.map (MulAut.conj g).toMonoidHom ≤ G₁ ∨
      G₁.map (MulAut.conj g).toMonoidHom ≤ G₂ := fun g hg =>
    map_conj_le_or hW hfix₁₂ (fun Y hYW hYinv hY => RedPiece.eq_of_inv hr₁ hYW hYinv hY) hDtr
      hDsplit
      hcomm hcl₁ (hgD g hg)
  have hle₂ : ∀ g ∈ G, G₂.map (MulAut.conj g).toMonoidHom ≤ G₂ ∨
      G₂.map (MulAut.conj g).toMonoidHom ≤ G₁ := fun g hg =>
    map_conj_le_or (by rw [sup_comm]; exact hW) hfix₂₁
      (fun Y hYW hYinv hY => RedPiece.eq_of_inv hr₂ hYW hYinv hY) hDtr
      (fun d hd => (hDsplit d hd).symm)
      hcomm' hcl₂ (hgD g hg)
  have heq : ∀ {H L : Subgroup (MulAut V)} {g : MulAut V},
      H.map (MulAut.conj g).toMonoidHom ≤ L → Nat.card L ≤ Nat.card H →
      H.map (MulAut.conj g).toMonoidHom = L := fun hle hc =>
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj]; exact hc)
  have hbot₁₂ : ¬ G₂ ≤ G₁ := fun hle => hG₂ne (by
    rw [eq_bot_iff, ← hinf]
    exact le_inf hle le_rfl)
  have hbot₂₁ : ¬ G₁ ≤ G₂ := fun hle => hG₁ne (by
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl hle)
  have hperm : ∀ g ∈ G, (G₁.map (MulAut.conj g).toMonoidHom = G₁ ∧
        G₂.map (MulAut.conj g).toMonoidHom = G₂) ∨
      (G₁.map (MulAut.conj g).toMonoidHom = G₂ ∧ G₂.map (MulAut.conj g).toMonoidHom = G₁) := by
    intro g hg
    rcases hle₁ g hg with h1 | h1
    · have e1 := heq h1 le_rfl
      rcases hle₂ g hg with h2 | h2
      · exact Or.inl ⟨e1, heq h2 le_rfl⟩
      · exfalso
        apply hbot₁₂
        apply le_of_map_conj_le (g := g)
        rw [e1]
        exact h2
    · rcases hle₂ g hg with h2 | h2
      · exfalso
        have e2 := heq h2 le_rfl
        apply hbot₂₁
        apply le_of_map_conj_le (g := g)
        rw [e2]
        exact h1
      · have c1 : Nat.card G₁ ≤ Nat.card G₂ := by
          rw [← card_map_conj G₁ g]
          exact Subgroup.card_le_of_le h1
        have c2 : Nat.card G₂ ≤ Nat.card G₁ := by
          rw [← card_map_conj G₂ g]
          exact Subgroup.card_le_of_le h2
        exact Or.inr ⟨heq h1 c2, heq h2 c1⟩
  obtain ⟨g₀, hg₀G, hg₀⟩ : ∃ g ∈ G, G₁.map (MulAut.conj g).toMonoidHom = G₂ := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ g ∈ G, G₁.map (MulAut.conj g).toMonoidHom = G₁ := fun g hg =>
      ((hperm g hg).resolve_right fun h' => hcon g hg h'.1).1
    have hKle : K ≤ G₁ := by
      refine conjClosure_le fun g hg z hz => ?_
      have hz₁ : z ∈ G₁ := (Subgroup.zpowers_le.2 ha₁) hz
      rw [← hall g hg]
      exact ⟨z, hz₁, rfl⟩
    exact hbot₁₂ (hG₂K.trans hKle)
  have hg₀' : G₂.map (MulAut.conj g₀).toMonoidHom = G₁ :=
    ((hperm g₀ hg₀G).resolve_left fun h' => hbot₁₂ (by rw [← h'.1, hg₀])).2
  have hN : ∀ g ∈ G, G₁.map (MulAut.conj g).toMonoidHom = G₁ → g ∈ K := by
    intro g hg hg₁
    have hg₂ : G₂.map (MulAut.conj g).toMonoidHom = G₂ :=
      ((hperm g hg).resolve_right fun h' => hbot₁₂ (by rw [← h'.1, hg₁])).2
    have hn₁ : ∀ x ∈ G₁, g * x * g⁻¹ ∈ G₁ := fun x hx => by rw [← hg₁]; exact ⟨x, hx, rfl⟩
    have hn₂ : ∀ x ∈ G₂, g * x * g⁻¹ ∈ G₂ := fun x hx => by rw [← hg₂]; exact ⟨x, hx, rfl⟩
    obtain ⟨k₁, hk₁, hgk₁⟩ := RedPiece.exists_eq_on hV2 hr₁ ha₁ htr hn₁
    obtain ⟨k₂, hk₂, hgk₂⟩ := RedPiece.exists_eq_on hV2 hr₂ hd₂ hd₂tr hn₂
    have hk₂W : ∀ w ∈ commV G₂, k₂ w ∈ commV G₂ := fun w hw =>
      G6.apply_mem_commV (fun x hx => G₂.mul_mem (G₂.mul_mem hk₂ hx) (G₂.inv_mem hk₂)) hw
    have : g = k₁ * k₂ := by
      ext v
      have hv : v ∈ commV G₁ ⊔ commV G₂ := by rw [hW]; trivial
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.1 hv
      rw [map_mul, hgk₁ w₁ hw₁, hgk₂ w₂ hw₂, MulAut.mul_apply, map_mul, hfix₂₁ k₂ hk₂ w₁ hw₁,
        map_mul, hfix₁₂ k₁ hk₁ _ (hk₂W w₂ hw₂)]
    rw [this]
    exact K.mul_mem (hG₁K hk₁) (hG₂K hk₂)
  have h12n : G₁ ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := le_normalizer_of_commute hcomm
  have hg₀sq : g₀ * g₀ ∈ K := by
    refine hN _ (G.mul_mem hg₀G hg₀G) ?_
    rw [map_conj_mul, hg₀, hg₀']
  obtain ⟨k₀, hk₀, k₁, hk₁, hk₀₁⟩ := mem_sup_of_normalizer h12n (hsup ▸ hg₀sq)
  have hgk₀ : g₀ * k₀ * g₀⁻¹ ∈ G₂ := by rw [← hg₀]; exact ⟨k₀, hk₀, rfl⟩
  have hgk₁ : g₀ * k₁ * g₀⁻¹ ∈ G₁ := by rw [← hg₀']; exact ⟨k₁, hk₁, rfl⟩
  have hprod : (g₀ * k₁ * g₀⁻¹) * (g₀ * k₀ * g₀⁻¹) = k₀ * k₁ := by
    have hc := hcomm _ hgk₁ _ hgk₀
    rw [hc]
    calc g₀ * k₀ * g₀⁻¹ * (g₀ * k₁ * g₀⁻¹) = g₀ * (k₀ * k₁) * g₀⁻¹ := by group
      _ = g₀ * (g₀ * g₀) * g₀⁻¹ := by rw [hk₀₁]
      _ = g₀ * g₀ := by group
      _ = k₀ * k₁ := hk₀₁
  obtain ⟨e1, -⟩ := G6.eq_of_mul_eq_mul_of_disjoint (disjoint_iff.2 hinf) hgk₁ hk₀ hgk₀ hk₁ hprod
  set t := g₀ * k₀⁻¹ with ht
  have hk₀K : k₀ ∈ K := hG₁K hk₀
  have htG : t ∈ G := G.mul_mem hg₀G (G.inv_mem (hKG hk₀K))
  have ht2 : t ^ 2 = 1 := by
    have h1 : g₀ * k₁ = k₀ * g₀ := by rw [← e1]; group
    have h2 : k₀⁻¹ * g₀ = g₀ * k₁⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul]
      have : k₀ * (g₀ * k₁⁻¹) = g₀ := by rw [← mul_assoc, ← h1]; group
      exact this.symm
    rw [sq, ht]
    calc g₀ * k₀⁻¹ * (g₀ * k₀⁻¹) = g₀ * (k₀⁻¹ * g₀) * k₀⁻¹ := by group
      _ = g₀ * (g₀ * k₁⁻¹) * k₀⁻¹ := by rw [h2]
      _ = (g₀ * g₀) * k₁⁻¹ * k₀⁻¹ := by group
      _ = (k₀ * k₁) * k₁⁻¹ * k₀⁻¹ := by rw [hk₀₁]
      _ = 1 := by group
  have hk₀G₁ : G₁.map (MulAut.conj k₀⁻¹).toMonoidHom = G₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer (G₁.inv_mem hk₀))
  have ht₀ : G₁.map (MulAut.conj t).toMonoidHom = G₂ := by
    rw [ht, map_conj_mul, hk₀G₁, hg₀]
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, map_conj_one] at ht₀
    exact hbot₂₁ ht₀.le
  have hGt : G = K ⊔ Subgroup.zpowers t := by
    refine le_antisymm (fun g hg => ?_) (sup_le hKG (Subgroup.zpowers_le.2 htG))
    rcases hperm g hg with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Subgroup.mem_sup_left (hN g hg h1)
    · have hgt : g * t ∈ K := hN _ (G.mul_mem hg htG) (by rw [map_conj_mul, ht₀, h2])
      have : g = (g * t) * t⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgt)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
  have h4 : ¬ ∃ T, IsSylowTwoOf T G ∧ a ∈ T ∧ ∀ x ∈ T, x * a = a * x := by
    rintro ⟨T, ⟨hTG, -, hTi⟩, -, hcent⟩
    have hTK : T ≤ K := by
      intro x hx
      refine hN x (hTG hx) ?_
      rcases hperm x (hTG hx) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exfalso
        have hxa : x * a * x⁻¹ = a := by rw [hcent x hx]; group
        have : a ∈ G₁ ⊓ G₂ := ⟨ha₁, by rw [← h1, ← hxa]; exact ⟨a, ha₁, rfl⟩⟩
        rw [hinf, Subgroup.mem_bot] at this
        exact ha1 this
    have hKt : t ∉ K := by
      intro htK
      have : G₁.map (MulAut.conj t).toMonoidHom = G₁ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 ((hsup ▸ sup_le_normalizer_left hcomm) htK)
      rw [ht₀] at this
      exact hbot₂₁ this.ge
    have hdvd : K.relIndex G ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨t, htG, fun b hb => ?_⟩
      rcases hperm b hb with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Or.inr (hN b hb h1)
      · exact Or.inl (hN _ (G.mul_mem hb htG) (by rw [map_conj_mul, ht₀, h2]))
    have hne1 : K.relIndex G ≠ 1 := fun h1 => hKt (Subgroup.relIndex_eq_one.1 h1 htG)
    have h2 : K.relIndex G = 2 := ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne1
    have hmul := Subgroup.relIndex_mul_relIndex T K G hTK hKG
    apply hTi
    change 2 ∣ T.relIndex G
    rw [← hmul, h2]
    exact Dvd.intro_left _ rfl
  obtain ⟨hmod₁, hfac₁⟩ := RedPiece.types hr₁
  obtain ⟨hmod₂, hfac₂⟩ := RedPiece.types hr₂
  exact conclusion_of_pair hsup hinf hcomm hW (fun w hw => mem_fixV.2 fun g hg => hfix₁₂ g hg w hw)
    (fun w hw => mem_fixV.2 fun g hg => hfix₂₁ g hg w hw) ha₁ hperm hmod₁ hmod₂ hfac₁ hfac₂ htG
    ht1 ht2 hGt ht₀ h4

theorem conclusion_of_case3 [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (h : Hyp61 G a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    (hC : B56Case3 (conjClosure (Subgroup.zpowers a) G)) : Conclusion G a := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hW, hfix₁₂, hfix₂₁, hr₁, hr₂, hDsplit, hd₁, hd₂⟩ :=
    case3_split hV2 h htr hC
  have haD : a ∈ transSet G a := ⟨1, G.one_mem, by group⟩
  rcases hDsplit a haD with ha | ha
  · exact conclusion_of_split hV2 h htr hsup hinf hcomm hW hfix₁₂ hfix₂₁ hr₁ hr₂ hDsplit hd₂ ha
  · exact conclusion_of_split hV2 h htr (by rw [sup_comm]; exact hsup)
      (by rw [inf_comm]; exact hinf) (fun x hx y hy => (hcomm y hy x hx).symm)
      (by rw [sup_comm]; exact hW) hfix₂₁ hfix₁₂ hr₂ hr₁ (fun d hd => (hDsplit d hd).symm) hd₁ ha

end CFSG.Quasithin.G64
