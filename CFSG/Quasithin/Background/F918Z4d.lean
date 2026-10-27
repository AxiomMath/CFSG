module

public import CFSG.Quasithin.Background.F918Z4dAux
public import CFSG.Quasithin.Background.F918Z6Def

public section

namespace CFSG.Quasithin

namespace Z4d

theorem eq_one_of_commutes {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}
    {s : MulAut V} (hZ : Z37 D X G T' s) {a : MulAut V} (ha2 : a * a = 1)
    (hD : ∀ y ∈ D, a * y = y * a) (hX : ∀ x ∈ X, a * x = x * a) : a = 1 := by
  have hcent : D ⊔ X ≤ Subgroup.centralizer {a} := by
    refine sup_le (fun y hy => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hD y hy).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hX x hx).symm
  have hCinv : ∀ g ∈ D ⊔ X, ∀ u ∈ fixV (Subgroup.zpowers a), g u ∈ fixV (Subgroup.zpowers a) := by
    intro g hg u hu
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 (hcent hg)
    exact mem_fixV_zpowers_of_comm hga.symm hu
  rcases hZ.irr _ hCinv with h | h
  · ext v
    have hw : a v * v⁻¹ ∈ fixV (Subgroup.zpowers a) := by
      rw [mem_fixV_zpowers_iff, map_mul, map_inv]
      have h1 : a (a v) = v := by simpa using congrArg (fun f : MulAut V => f v) ha2
      rw [h1]
      have hx2 : (a v * v⁻¹) * (a v * v⁻¹) = 1 := by
        have := hZ.exp (a v * v⁻¹)
        rwa [pow_two] at this
      have hxy : (a v * v⁻¹) * (v * (a v)⁻¹) = 1 := by
        calc (a v * v⁻¹) * (v * (a v)⁻¹) = (a v * (a v)⁻¹) * (v⁻¹ * v) := by ac_rfl
          _ = 1 := by simp
      exact mul_left_cancel (hxy.trans hx2.symm)
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hw
    simpa using hw
  · ext v
    have : v ∈ fixV (Subgroup.zpowers a) := by rw [h]; trivial
    simpa [mem_fixV_zpowers_iff] using this

theorem not_trivial_on_fixV_of_swap {V : Type} [CommGroup V] [Finite V]
    {D X G T' : Subgroup (MulAut V)} {t : MulAut V} (hZ : Z37 D X G T' t) (ht2 : t * t = 1)
    {a : MulAut V} (ha2 : a * a = 1) (hat : a * t = t * a) (haD : ∀ y ∈ D, a * y * a⁻¹ ∈ D)
    (hne : ∃ y ∈ D, a * y ≠ y * a) :
    ∃ v ∈ fixV (Subgroup.zpowers t), a v ≠ v := by
  by_contra hcon
  push Not at hcon
  have := hZ.simple
  have hX : ∀ y ∈ D, t * y * t⁻¹ ∈ X := fun y hy => by
    rw [hZ.swapDX]
    exact ⟨y, hy, rfl⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  set φ : ↥D →* MulAut V := diagHom D X t hX hZ.comm with hφ
  have hφt : ∀ y : ↥D, t * φ y = φ y * t := fun y => diagHom_comm ht2 y
  have hφC : ∀ y : ↥D, ∀ v ∈ fixV (Subgroup.zpowers t), φ y v ∈ fixV (Subgroup.zpowers t) :=
    fun y v hv => mem_fixV_zpowers_of_comm (hφt y) hv
  let K : Subgroup ↥D := (centSub (fixV (Subgroup.zpowers t))).comap φ
  have hKmem : ∀ y : ↥D, y ∈ K ↔ ∀ v ∈ fixV (Subgroup.zpowers t), φ y v = v := fun y => Iff.rfl
  have hKn : K.Normal := ⟨fun n hn g => by
    rw [hKmem] at hn ⊢
    intro v hv
    have h1 : φ g⁻¹ v ∈ fixV (Subgroup.zpowers t) := hφC g⁻¹ v hv
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hn _ h1, ← MulAut.mul_apply,
      ← map_mul]
    simp⟩
  have hKy : ∀ y : ↥D, (⟨a * y * a⁻¹, haD y y.2⟩ * y⁻¹ : ↥D) ∈ K := by
    intro y
    rw [hKmem]
    intro v hv
    have hconj : φ ⟨a * y * a⁻¹, haD y y.2⟩ = a * φ y * a⁻¹ := diagHom_conj a hat haD y
    have hv1 : φ y⁻¹ v ∈ fixV (Subgroup.zpowers t) := hφC y⁻¹ v hv
    have h3 : φ y (φ y⁻¹ v) = v := by
      rw [← MulAut.mul_apply, ← map_mul]
      simp
    rw [map_mul, hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hainv,
      hcon _ hv1, h3]
    exact hcon v hv
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
  · obtain ⟨y, hy, hay⟩ := hne
    apply hay
    have h1 := hKy ⟨y, hy⟩
    rw [hK, Subgroup.mem_bot] at h1
    have h2 : a * y * a⁻¹ = y := by
      have := congrArg Subtype.val h1
      simpa [mul_inv_eq_one] using this
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [h2]
  · obtain ⟨y, hy, z, hz, hyz⟩ := hZ.nonab
    have hall : ∀ w : ↥D, ∀ v ∈ fixV (Subgroup.zpowers t), φ w v = v :=
      fun w => (hKmem w).1 (by rw [hK]; trivial)
    have hcomm : φ ⟨y, hy⟩ * φ ⟨z, hz⟩ = φ ⟨z, hz⟩ * φ ⟨y, hy⟩ :=
      comm_of_fixing hZ.exp ht2 (hφt _) (hφt _) (hall _) (hall _)
    have hinj : Function.Injective φ := diagHom_injective hZ.nonab
    rw [← map_mul, ← map_mul] at hcomm
    exact hyz (congrArg Subtype.val (hinj hcomm))

theorem rkIdx_fixV_succ_le_of_swap {V : Type} [CommGroup V] [Finite V]
    {D X G T' : Subgroup (MulAut V)} {t : MulAut V} (hZ : Z37 D X G T' t) (ht2 : t * t = 1)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) (htA : t ∈ A) {a : MulAut V} (haA : a ∈ A)
    (haD : D.map (MulAut.conj a).toMonoidHom = D) (ha1 : a ≠ 1) :
    rkIdx (fixV (Subgroup.zpowers t)) + 1 ≤ rkIdx (fixV A) := by
  have hat : a * t = t * a := hA.1 a haA t htA
  have ha2 : a * a = 1 := by
    have := hA.2 a haA
    rwa [pow_two] at this
  have haD' : ∀ y ∈ D, a * y * a⁻¹ ∈ D := fun y hy => by
    have : a * y * a⁻¹ ∈ D.map (MulAut.conj a).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [haD] at this
  have hne : ∃ y ∈ D, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    refine ha1 (eq_one_of_commutes hZ ha2 hcon fun x hx => ?_)
    rw [hZ.swapDX] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : Commute a t := hat
    have h2 : Commute a y := hcon y hy
    exact (h1.mul_right h2).mul_right h1.inv_right
  obtain ⟨v, hv, hav⟩ := not_trivial_on_fixV_of_swap hZ ht2 ha2 hat haD' hne
  have hle : fixV A ≤ fixV (Subgroup.zpowers t) := fun w hw =>
    mem_fixV_zpowers_iff.2 (hw t htA)
  have hlt : fixV A ≠ fixV (Subgroup.zpowers t) := fun h => by
    have hv' : v ∈ fixV A := by rw [h]; exact hv
    exact hav (hv' a haA)
  have hrk : rk (fixV A) < rk (fixV (Subgroup.zpowers t)) := by
    by_contra h
    exact hlt (eq_of_le_of_rk_le hZ.exp hle (not_lt.1 h))
  have h1 := rk_add_rkIdx (fixV A)
  have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
  omega

theorem rk_eq_rk_normalizer_add_one {V : Type} [CommGroup V] [Finite V]
    {D X G T' : Subgroup (MulAut V)} {t : MulAut V} (hZ : Z37 D X G T' t) (ht2 : t * t = 1)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) (htA : t ∈ A)
    (hperm : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D ∨
      D.map (MulAut.conj a).toMonoidHom = X) :
    rk A = rk ↥(A ⊓ Subgroup.normalizer (D : Set (MulAut V))) + 1 := by
  have _ := ht2
  set N : Subgroup (MulAut V) := Subgroup.normalizer (D : Set (MulAut V)) with hN
  have hmemN : ∀ g : MulAut V, g ∈ N ↔ D.map (MulAut.conj g).toMonoidHom = D := fun g =>
    Subgroup.mem_normalizer_iff_map_conj_eq
  have htN : t ∉ N := by
    intro h
    have hXD : X = D := hZ.swapDX.trans ((hmemN t).1 h)
    obtain ⟨a, ha, b, hb, hab⟩ := hZ.nonab
    exact hab (hZ.comm a ha b (by rw [hXD]; exact hb))
  have hc : ∀ c : MulAut V, c ∈ A → (c ∈ N ↔ ¬ c * t ∈ N) := by
    intro c hc
    have hc2 : c * c = 1 := by
      have := hA.2 c hc
      rwa [pow_two] at this
    constructor
    · intro hcN hctN
      apply htN
      have : t = c⁻¹ * (c * t) := by group
      rw [this]
      exact N.mul_mem (N.inv_mem hcN) hctN
    · intro hnot
      by_contra hcN
      apply hnot
      have h1 : D.map (MulAut.conj c).toMonoidHom = X := by
        rcases hperm c hc with h | h
        · exact absurd ((hmemN c).2 h) hcN
        · exact h
      have h2 : X.map (MulAut.conj c).toMonoidHom = D := by
        rw [← h1, ← map_conj_mul, hc2, map_conj_one]
      rw [hmemN, map_conj_mul, ← hZ.swapDX, h2]
  have hidx : N.relIndex A = 2 := by
    show (N.subgroupOf A).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htA⟩, fun c => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases h : (c : MulAut V) ∈ N
    · exact Or.inr ⟨h, (hc c c.2).1 h⟩
    · exact Or.inl ⟨not_not.1 (fun h' => h ((hc c c.2).2 h')), h⟩
  have hcard : Nat.card A = 2 * Nat.card ↥(A ⊓ N) := by
    have := Subgroup.relIndex_mul_card N A
    rw [hidx, inf_comm N A] at this
    exact this.symm
  unfold rk
  rw [hcard, padicValNat.mul (by norm_num) (card_subgroup_pos _).ne', padicValNat_self]
  omega

end Z4d

end CFSG.Quasithin
