module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal

namespace StdPosExc

theorem exists_toralPos_of_toral_isog {U C : Type} [Group U] [Group C] {ι : U →* C}
    (hι : Function.Surjective ι) (hZ : Subgroup.center C = ⊥)
    (hkerι : ι.ker ≤ Subgroup.center U) {V : Subgroup C} {G : Type} [Group G] [Finite G]
    {ψ : U →* G} {p r : ℕ} {Bs : Subgroup G} (hker : ψ.ker ≤ Subgroup.center U)
    (hT : ∀ E : Subgroup C, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      ∃ g : C, E.map (MulAut.conj g).toMonoidHom ≤ V)
    (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hc : p ^ r * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : U,
      (∀ b ∈ Bs, ∃ v : U, ι v ∈ V ∧ ∀ z, b * (ψ.comp (MulAut.conj s).toMonoidHom) z * b⁻¹ =
        (ψ.comp (MulAut.conj s).toMonoidHom) (v * z * v⁻¹)) ∧
      (Finite V → Nat.card V ≤ p ^ r → ∀ c ∈ V, ∃ b ∈ Bs, ∃ v : U, ι v = c ∧
        ∀ z, b * (ψ.comp (MulAut.conj s).toMonoidHom) z * b⁻¹ =
          (ψ.comp (MulAut.conj s).toMonoidHom) (v * z * v⁻¹)) := by
  have hZU : Subgroup.center U ≤ ι.ker := fun z hz => by
    have h1 : ι z ∈ Subgroup.center C := Subgroup.map_center_le_center hι ⟨z, hz, rfl⟩
    rwa [hZ, Subgroup.mem_bot] at h1
  have hex : ∀ b ∈ Bs, ∃ u : U, ∀ z, b * ψ z * b⁻¹ = ψ (u * z * u⁻¹) := by
    intro b hb
    obtain ⟨_, ⟨w, rfl⟩, hg⟩ := hinn b hb
    refine ⟨w⁻¹, fun z => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hg (ψ (w⁻¹ * z * w)) ⟨_, rfl⟩
    have hz : ψ z = ψ w * ψ (w⁻¹ * z * w) * (ψ w)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; congr 1; group
    rw [inv_inv, hz]
    calc b * (ψ w * ψ (w⁻¹ * z * w) * (ψ w)⁻¹) * b⁻¹
        = b * ψ w * ψ (w⁻¹ * z * w) * (b * ψ w)⁻¹ := by group
      _ = ψ (w⁻¹ * z * w) * (b * ψ w) * (b * ψ w)⁻¹ := by rw [← h1]
      _ = ψ (w⁻¹ * z * w) := by group
  have huniq : ∀ u v : U, (∀ z, ψ (u * z * u⁻¹) = ψ (v * z * v⁻¹)) → ι u = ι v := by
    intro u v h
    have hmem : ι (v⁻¹ * u) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨z, rfl⟩ := hι w
      have hk : (v * z * v⁻¹)⁻¹ * (u * z * u⁻¹) ∈ ι.ker :=
        hZU (hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h z, inv_mul_cancel]))
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
      simp only [map_mul, map_inv] at hk ⊢
      calc ι z * ((ι v)⁻¹ * ι u) = (ι v)⁻¹ * (ι v * ι z * (ι v)⁻¹) * ι u := by group
        _ = (ι v)⁻¹ * (ι u * ι z * (ι u)⁻¹) * ι u := by rw [hk]
        _ = (ι v)⁻¹ * ι u * ι z := by group
    rw [hZ, Subgroup.mem_bot, map_mul, map_inv, inv_mul_eq_one] at hmem
    exact hmem.symm
  choose! u hu using hex
  have hmul : ∀ x ∈ Bs, ∀ y ∈ Bs, ι (u (x * y)) = ι (u x) * ι (u y) := by
    intro x hx y hy
    rw [← map_mul]
    refine huniq _ _ fun z => ?_
    have e : u x * u y * z * (u x * u y)⁻¹ = u x * (u y * z * (u y)⁻¹) * (u x)⁻¹ := by group
    rw [← hu _ (Bs.mul_mem hx hy), e, ← hu x hx, ← hu y hy]; group
  let θ : ↥Bs →* C := MonoidHom.mk' (fun b => ι (u b)) fun x y => hmul x x.2 y y.2
  have hkerC : ∀ b : ↥Bs, θ b = 1 → (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    intro b hb1
    change ι (u b) = 1 at hb1
    rw [Subgroup.mem_centralizer_iff]; rintro _ ⟨y, rfl⟩
    have h1 := hu b b.2 y
    rw [← Subgroup.mem_center_iff.1 (hkerι hb1) y, mul_inv_cancel_right] at h1
    calc ψ y * (b : G) = (b : G) * ψ y * (b : G)⁻¹ * b := by rw [h1]
      _ = (b : G) * ψ y := by group
  have hkerle : Nat.card θ.ker ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥Bs) : G), (x : ↥Bs).2, hkerC x.1 (MonoidHom.mem_ker.mp x.2)⟩)
      fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hcard : Nat.card ↥Bs ≤
      Nat.card θ.range * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    rw [← Subgroup.card_ker_mul_card_range θ, mul_comm]
    exact Nat.mul_le_mul_left _ hkerle
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := Nat.card_pos
  have hr : p ^ r ≤ Nat.card θ.range := Nat.le_of_mul_le_mul_right (hc.trans hcard) hpos
  have hXel : IsElemAbelian p θ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      change θ x * θ y = θ y * θ x
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      have hx : x ^ p = 1 := Subtype.ext (by simpa using hBs.2 x x.2)
      rw [← map_pow, hx, map_one]
  obtain ⟨g, hg⟩ := hT θ.range hXel hr
  obtain ⟨g, rfl⟩ := hι g
  have hact : ∀ b ∈ Bs, ∀ z, b * (ψ.comp (MulAut.conj g⁻¹).toMonoidHom) z * b⁻¹ =
      (ψ.comp (MulAut.conj g⁻¹).toMonoidHom) (g * u b * g⁻¹ * z * (g * u b * g⁻¹)⁻¹) := by
    intro b hb z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hu b hb]
    congr 1
    group
  refine ⟨g⁻¹, fun b hb => ⟨g * u b * g⁻¹, ?_, hact b hb⟩, fun hfin hV c hcV => ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact hg ⟨θ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  ·
    have hM : θ.range.map (MulAut.conj (ι g)).toMonoidHom = V := by
      refine Subgroup.eq_of_le_of_card_ge hg (hV.trans (hr.trans_eq ?_))
      exact Nat.card_congr (θ.range.equivMapOfInjective (MulAut.conj (ι g)).toMonoidHom
        (MulAut.conj (ι g)).injective).toEquiv
    rw [← hM] at hcV
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hcV
    refine ⟨b, b.2, g * u b * g⁻¹, ?_, hact b b.2⟩
    simp [θ, MulAut.conj_apply]

theorem exists_stdPos_of_toral_isog {U C : Type} [Group U] [Group C]
    {Δ : UniversalRootDatum U} {ι : U →* C} (hι : Function.Surjective ι)
    (hZ : Subgroup.center C = ⊥) (hkerι : ι.ker ≤ Subgroup.center U) {V : Subgroup C}
    (hV : V.comap ι ≤ ggTorus Δ) {G : Type} [Group G] [Finite G] {ψ : U →* G} {p r : ℕ}
    {Bs : Subgroup G} (hker : ψ.ker ≤ Subgroup.center U)
    (hT : ∀ E : Subgroup C, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      ∃ g : C, E.map (MulAut.conj g).toMonoidHom ≤ V)
    (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hc : p ^ r * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : U, GGKGPosStdPos Δ (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  obtain ⟨s, hs, -⟩ := exists_toralPos_of_toral_isog hι hZ hkerι hker hT hBs hinn hc
  refine ⟨s, fun b hb γ _ => ?_⟩
  obtain ⟨v, hv, hbv⟩ := hs b hb
  exact ⟨v, hV hv, fun z _ => hbv z⟩

theorem exists_stdPos_of_toral {U : Type} [Group U] {Δ : UniversalRootDatum U}
    {V : Subgroup U} {G : Type} [Group G] [Finite G] {ψ : U →* G} {p r : ℕ} {Bs : Subgroup G}
    (hZ : Subgroup.center U = ⊥) (hker : ψ.ker ≤ Subgroup.center U) (hV : V ≤ ggTorus Δ)
    (hT : ∀ E : Subgroup U, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      ∃ g : U, E.map (MulAut.conj g).toMonoidHom ≤ V)
    (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hc : p ^ r * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : U, GGKGPosStdPos Δ (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  exact exists_stdPos_of_toral_isog (ι := MonoidHom.id U) (fun x => ⟨x, rfl⟩) hZ
    (MonoidHom.ker_id.trans_le bot_le) ((Subgroup.comap_id V).trans_le hV) hker hT hBs hinn hc

end StdPosExc

end CFSG.StandardType

end
