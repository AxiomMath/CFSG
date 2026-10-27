module

public import CFSG.Quasithin.Background.F918YC0
public import CFSG.Quasithin.Background.F918D4
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.Quasithin

private theorem yc_map_mul {W : Type} [CommGroup W] (a b : MulAut W) (U : Subgroup W) :
    U.map (a * b).toMonoidHom = (U.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem yc_map_one {W : Type} [CommGroup W] (U : Subgroup W) :
    U.map (1 : MulAut W).toMonoidHom = U := by
  ext x
  simp

private theorem yc_mem_iff_of_map_eq {W : Type} [CommGroup W] {V : Subgroup W} {g : MulAut W}
    (hg : V.map g.toMonoidHom = V) (v : W) : g v ∈ V ↔ v ∈ V := by
  have h1 : g v ∈ V.map g.toMonoidHom ↔ v ∈ V := Subgroup.mem_map_iff_mem g.injective
  rw [hg] at h1
  exact h1

private theorem yc_mem_normalizer_of_comm {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {g : MulAut W} (hg : ∀ x ∈ L, g * x = x * g) :
    g ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [mul_inv_eq_iff_eq_mul.2 (hg x hx)]
    exact hx
  · intro hx
    have h1 : g * (g * x * g⁻¹) = g * x := by
      rw [hg _ hx]
      group
    rw [mul_left_cancel h1] at hx
    exact hx

private theorem yc_eq_of_agree {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} {σ : MulAut W} (h : N4Base W L V σ) {a b : MulAut W} (ha : a ∈ L)
    (hb : b ∈ L) (hab : ∀ v ∈ V, a v = b v) : a = b := by
  have h1 : b⁻¹ * a = 1 := by
    refine cover_faithful h.hexp L V h.hinv h.hcomm h.hnat h.hZ _ (L.mul_mem (L.inv_mem hb) ha) ?_
    intro v hv
    rw [MulAut.mul_apply, hab v hv]
    simp
  exact (inv_mul_eq_one.1 h1).symm

private theorem yc_comm_of_triv {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} {σ : MulAut W} (h : N4Base W L V σ) {k : MulAut W}
    (hkN : k ∈ Subgroup.normalizer (L : Set (MulAut W))) (hk : ∀ v ∈ V, k v = v) :
    ∀ x ∈ L, k * x = x * k := by
  intro x hx
  have hkL := Subgroup.mem_normalizer_iff.1 hkN
  have hx' : k * x * k⁻¹ * x⁻¹ ∈ L := L.mul_mem ((hkL x).1 hx) (L.inv_mem hx)
  have hkinv : ∀ v ∈ V, k⁻¹ v = v := fun v hv => by
    calc k⁻¹ v = k⁻¹ (k v) := by rw [hk v hv]
      _ = v := by simp
  have h1 : k * x * k⁻¹ * x⁻¹ = 1 := by
    refine cover_faithful h.hexp L V h.hinv h.hcomm h.hnat h.hZ _ hx' ?_
    intro v hv
    have hxv : x⁻¹ v ∈ V := h.hinv _ (L.inv_mem hx) v hv
    simp only [MulAut.mul_apply]
    rw [hkinv _ hxv]
    have : x (x⁻¹ v) = v := by simp
    rw [this, hk v hv]
  calc k * x = k * x * k⁻¹ * x⁻¹ * x * k := by group
    _ = x * k := by rw [h1]; group

private theorem yc_triv_on_V {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} {σ : MulAut W} (h : N4Base W L V σ) {g : MulAut W}
    (hg : ∀ x ∈ L, g * x = x * g) : ∀ v ∈ V, g v = v := by
  have hgN := yc_mem_normalizer_of_comm hg
  have hgL := Subgroup.mem_normalizer_iff.1 hgN
  have huni : ∀ S : Subgroup W, S ≤ V → (∀ x ∈ L, ∀ s ∈ S, x s ∈ S) →
      S = ⊥ ∨ S = V ⊓ fixV L ∨ S = V := fun S hSV hS =>
    cover_uniserial h.hexp L V h.hinv h.hcomm h.hnat h.hZ S hSV hS
  rcases cover_map_eq_or h.hexp L V h.hinv h.hcomm h.hnat h.hZ huni σ h.hσL h.hne h.hdyn h.hsum
    h.hint g hgL with hgV | hgσ
  ·
    obtain ⟨l, hl, hgl⟩ := cover_normalizer_stab h.hexp L V h.hinv h.hcomm h.hnat h.hZ g hgL
      (yc_mem_iff_of_map_eq hgV)
    have hl1 : l = 1 := by
      refine cover_center_trivial h.hexp L V h.hinv h.hcomm h.hnat h.hZ l hl fun x hx => ?_
      refine yc_eq_of_agree h (L.mul_mem hl hx) (L.mul_mem hx hl) fun v hv => ?_
      calc (l * x) v = l (x v) := rfl
        _ = g (x v) := (hgl _ (h.hinv x hx v hv)).symm
        _ = x (g v) := by simpa [MulAut.mul_apply] using DFunLike.congr_fun (hg x hx) v
        _ = x (l v) := by rw [hgl v hv]
        _ = (x * l) v := rfl
    intro v hv
    rw [hgl v hv, hl1]
    rfl
  ·
    exfalso
    have hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff.2 h.hσL
    have hpN : σ⁻¹ * g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hσN) hgN
    have hpV : V.map (σ⁻¹ * g).toMonoidHom = V := by
      rw [yc_map_mul, hgσ, ← yc_map_mul, inv_mul_cancel, yc_map_one]
    obtain ⟨l₀, hl₀, hl₀V⟩ := cover_normalizer_stab h.hexp L V h.hinv h.hcomm h.hnat h.hZ
      (σ⁻¹ * g) (Subgroup.mem_normalizer_iff.1 hpN) (yc_mem_iff_of_map_eq hpV)
    obtain ⟨k, hk⟩ : ∃ k : MulAut W, k = g⁻¹ * (σ * l₀) := ⟨_, rfl⟩
    have hkN : k ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [hk]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN)
        (Subgroup.mul_mem _ hσN (Subgroup.le_normalizer hl₀))
    have hkV : ∀ v ∈ V, k v = v := by
      intro v hv
      have h1 : σ (l₀ v) = g v := by
        rw [← hl₀V v hv]
        simp [MulAut.mul_apply]
      rw [hk, MulAut.mul_apply, MulAut.mul_apply, h1]
      simp
    have hkc := yc_comm_of_triv h hkN hkV
    have e : σ * l₀ = g * k := by rw [hk]; group
    apply h.hdyn
    refine ⟨l₀⁻¹, L.inv_mem hl₀, fun x hx => ?_⟩
    rw [inv_inv]
    calc σ * l₀ * x = g * k * x := by rw [e]
      _ = g * (k * x) := mul_assoc _ _ _
      _ = g * (x * k) := by rw [hkc x hx]
      _ = g * x * k := (mul_assoc _ _ _).symm
      _ = x * g * k := by rw [hg x hx]
      _ = x * (g * k) := mul_assoc _ _ _
      _ = x * (σ * l₀) := by rw [e]

theorem N4Base.centralizer_eq_one {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} {σ : MulAut W} (h : N4Base W L V σ) {g : MulAut W}
    (hg : ∀ x ∈ L, g * x = x * g) : g = 1 := by
  have h1 := yc_triv_on_V h hg
  have hg' : ∀ x ∈ L, (σ⁻¹ * g * σ) * x = x * (σ⁻¹ * g * σ) := by
    intro x hx
    have hx' : σ * x * σ⁻¹ ∈ L := (h.hσL x).1 hx
    calc σ⁻¹ * g * σ * x = σ⁻¹ * (g * (σ * x * σ⁻¹)) * σ := by group
      _ = σ⁻¹ * ((σ * x * σ⁻¹) * g) * σ := by rw [hg _ hx']
      _ = x * (σ⁻¹ * g * σ) := by group
  have h2 := yc_triv_on_V h hg'
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ V ⊔ V.map σ.toMonoidHom := by
    rw [h.hsum]
    trivial
  obtain ⟨v, hv, u, ⟨v', hv', rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hw
  have h3 : g (σ v') = σ v' := by
    have h4 : σ (σ⁻¹ (g (σ v'))) = σ v' := by
      have := congrArg σ (h2 v' hv')
      simpa [MulAut.mul_apply] using this
    simpa using h4
  show g (v * σ v') = v * σ v'
  rw [map_mul, h1 v hv, h3]

theorem secIsoL_of_commuting {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) {σ c : MulAut W}
    (hc : ∀ x ∈ L, c * x = x * c) (hcV : V.map c.toMonoidHom = V.map σ.toMonoidHom) :
    SecIsoL L V (V ⊓ fixV L) (V.map σ.toMonoidHom) (V.map σ.toMonoidHom ⊓ fixV L) := by
  have hcx : ∀ x ∈ L, ∀ w : W, c (x w) = x (c w) := fun x hx w => by
    simpa [MulAut.mul_apply] using DFunLike.congr_fun (hc x hx) w
  have hV'inv : ∀ x ∈ L, ∀ m ∈ V.map σ.toMonoidHom, x m ∈ V.map σ.toMonoidHom := by
    rw [← hcV]
    rintro x hx _ ⟨v, hv, rfl⟩
    exact ⟨x v, hinv x hx v hv, hcx x hx v⟩
  have hZinv : ∀ x ∈ L, ∀ z ∈ V ⊓ fixV L, x z ∈ V ⊓ fixV L := fun x hx z hz => by
    rw [hz.2 x hx]
    exact hz
  have hZ'inv : ∀ x ∈ L, ∀ z ∈ V.map σ.toMonoidHom ⊓ fixV L,
      x z ∈ V.map σ.toMonoidHom ⊓ fixV L := fun x hx z hz => by
    rw [hz.2 x hx]
    exact hz
  let φ : ↥V →* ↥(V.map σ.toMonoidHom) :=
    (c.toMonoidHom.comp V.subtype).codRestrict (V.map σ.toMonoidHom) fun v => by
      rw [← hcV]
      exact ⟨v, v.2, rfl⟩
  rw [B5.secIsoL_iff]
  refine ⟨inf_le_left, inf_le_left, fun γ u hu => hinv γ γ.2 u hu,
    fun γ z hz => hZinv γ γ.2 z hz, fun γ m hm => hV'inv γ γ.2 m hm,
    fun γ m hm => hZ'inv γ γ.2 m hm,
    (QuotientGroup.mk' ((V.map σ.toMonoidHom ⊓ fixV L).subgroupOf (V.map σ.toMonoidHom))).comp φ,
    ?_, ?_, ?_⟩
  ·
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : (m : W) ∈ V.map c.toMonoidHom := by
      rw [hcV]
      exact m.2
    obtain ⟨v, hv, hvm⟩ := hm
    refine ⟨⟨v, hv⟩, ?_⟩
    show (QuotientGroup.mk (φ ⟨v, hv⟩) : _) = QuotientGroup.mk m
    congr 1
    exact Subtype.ext hvm
  ·
    intro u
    show (QuotientGroup.mk (φ u) : _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show c (u : W) ∈ V.map σ.toMonoidHom ⊓ fixV L ↔ (u : W) ∈ V ⊓ fixV L
    constructor
    · rintro ⟨-, hfix⟩
      refine ⟨u.2, fun x hx => ?_⟩
      apply c.injective
      rw [hcx x hx u]
      exact hfix x hx
    · rintro ⟨-, hfix⟩
      refine ⟨?_, fun x hx => ?_⟩
      · rw [← hcV]
        exact ⟨u, u.2, rfl⟩
      · rw [← hcx x hx u, hfix x hx]
  ·
    intro γ u m hu hm hum
    have hum' := QuotientGroup.eq.1 hum
    rw [Subgroup.mem_subgroupOf] at hum'
    have hum'' : (c (u : W))⁻¹ * (m : W) ∈ V.map σ.toMonoidHom ⊓ fixV L := hum'
    show (QuotientGroup.mk (φ ⟨(γ : MulAut W) (u : W), hu⟩) : _) =
      QuotientGroup.mk ⟨(γ : MulAut W) (m : W), hm⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h3 := hZ'inv γ γ.2 _ hum''
    rw [map_mul, map_inv] at h3
    show (c ((γ : MulAut W) (u : W)))⁻¹ * (γ : MulAut W) (m : W) ∈ _
    rw [hcx γ γ.2 u]
    exact h3

end CFSG.Quasithin
