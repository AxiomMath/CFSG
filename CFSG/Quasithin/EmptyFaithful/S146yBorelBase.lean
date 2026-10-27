module

public import CFSG.Quasithin.EmptyFaithful.S146yB1Res
public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open CFSG.Open CFSG.QuasithinUnique

namespace CFSG.Quasithin

@[expose] def BorelRigid (Y : Type) [Group Y] : Prop :=
  ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → ∀ β : MulAut Y, (∀ y, β (β y) = y) →
    (∀ b ∈ Subgroup.normalizer (S : Set Y), β b = b) → β = 1

section Sylow

theorem exists_sylow_of_isSylowTwoOf_top {Y : Type} [Group Y] {S : Subgroup Y}
    (hS : IsSylowTwoOf S ⊤) : ∃ Q : Sylow 2 Y, (Q : Subgroup Y) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := (K1.isSylowTwoOf_top_iff.mp hS).2
  exact ⟨hS.2.1.toSylow hidx, rfl⟩

theorem exists_conj_of_isSylowTwoOf_top {Y : Type} [Group Y] [Finite Y] {U T : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) (hT : IsSylowTwoOf T ⊤) :
    ∃ g : Y, U.map (MulAut.conj g).toMonoidHom = T := by
  obtain ⟨P, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hU
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P Q
  exact ⟨g, congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hg⟩

theorem mem_sylow_of_involution_commute {Y : Type} [Group Y] [Finite Y] (Q : Sylow 2 Y) {x : Y}
    (hx : x * x = 1) (hc : ∀ s ∈ (Q : Subgroup Y), x * s = s * x) : x ∈ (Q : Subgroup Y) := by
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    have h2 : orderOf x ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((Q : Subgroup Y) : Set Y) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hc s hs).symm
  have hT : IsPGroup 2 (Subgroup.zpowers x ⊔ (Q : Subgroup Y) : Subgroup Y) :=
    hxp.to_sup_of_normal_right' Q.isPGroup' hxN
  have hmax := Q.is_maximal' hT le_sup_right
  rw [← hmax]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

end Sylow

section Transport

theorem BorelRigid.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : BorelRigid Y) :
    BorelRigid X := by
  intro S hS β hβ2 hβB
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hS
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map e.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
    exact hi
  let β' : MulAut Y := e.symm.trans (β.trans e)
  have hβ' : ∀ y, β' y = e (β (e.symm y)) := fun y => rfl
  have hone := h (S.map e.toMonoidHom) hS' β' (fun y => by
      rw [hβ', hβ', MulEquiv.symm_apply_apply, hβ2, MulEquiv.apply_symm_apply]) (fun b hb => by
      have hb' : b ∈ (Subgroup.normalizer (S : Set X)).map e.toMonoidHom := by
        rw [Subgroup.map_equiv_normalizer_eq]
        exact hb
      obtain ⟨b₀, hb₀, rfl⟩ := hb'
      rw [hβ']
      change e (β (e.symm (e b₀))) = e b₀
      rw [MulEquiv.symm_apply_apply, hβB b₀ hb₀])
  ext x
  have h1 := congrArg (fun φ : MulAut Y => e.symm (φ (e x))) hone
  simpa [hβ'] using h1

end Transport

section Glue

theorem isSylowTwoOf_top_subgroupOf' {Γ : Type} [Group Γ] {X S : Subgroup Γ} (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.subgroupOf X) (⊤ : Subgroup ↥X) := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact hS.2.2

theorem borelAutFree_of_rigid
    (hrig : ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ),
      (E2.IsBenderOf n Y ∨ (2 ≤ n ∧ (IsPSL 3 2 n Y ∨ E2.IsSp4Prime n Y))) → BorelRigid Y) :
    BorelAutFree := by
  intro Γ _ _ X B n g hfam hBorel hgN hg2 hgB x hx
  have hY := hrig ↥X n hfam
  obtain ⟨S, hS, rfl⟩ := hBorel
  let β : MulAut ↥X := X.normalizerMonoidHom ⟨g, hgN⟩
  have hβ : ∀ y : ↥X, ((β y : ↥X) : Γ) = g * y * g⁻¹ := fun y => rfl
  have hg2' : g * g = 1 := by rw [← sq]; exact hg2
  have hβ2 : ∀ y, β (β y) = y := by
    intro y
    apply Subtype.ext
    rw [hβ, hβ]
    calc g * (g * (y : Γ) * g⁻¹) * g⁻¹ = (g * g) * (y : Γ) * (g * g)⁻¹ := by group
      _ = y := by rw [hg2']; simp
  have hS' : IsSylowTwoOf (S.subgroupOf X) (⊤ : Subgroup ↥X) := isSylowTwoOf_top_subgroupOf' hS
  have hβB : ∀ b ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X), β b = b := by
    intro b hb
    have hb' : (b : Γ) ∈ Subgroup.normalizer ((S.subgroupOf X).map X.subtype : Set Γ) :=
      (A312.mem_normalizer_map_subtype_iff X (S.subgroupOf X) b).mp hb
    rw [Subgroup.map_subgroupOf_eq_of_le hS.1] at hb'
    apply Subtype.ext
    rw [hβ]
    have hcomm := hgB (b : Γ) ⟨b.2, hb'⟩
    calc g * (b : Γ) * g⁻¹ = (b : Γ) * g * g⁻¹ := by rw [hcomm]
      _ = b := by group
  have hone : β = 1 := hY (S.subgroupOf X) hS' β hβ2 hβB
  have h1 := congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : Γ)) hone
  simp only [hβ, MulAut.one_apply] at h1
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h1]

end Glue

section Inner

theorem core_of_sylow_conj {Y : Type} [Group Y] [Finite Y] {S₀ : Subgroup Y} (h₀ : IsSylowTwoOf S₀ ⊤)
    (hcore : ∀ x : Y, x * x = 1 → (∀ b ∈ Subgroup.normalizer (S₀ : Set Y), x * b = b * x) → x = 1)
    {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {x : Y} (hx : x * x = 1)
    (hc : ∀ b ∈ Subgroup.normalizer (S : Set Y), x * b = b * x) : x = 1 := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top h₀ hS
  have hN : Subgroup.normalizer (S : Set Y) =
      (Subgroup.normalizer (S₀ : Set Y)).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq, hg]
  have h1 : g⁻¹ * x * g = 1 := by
    apply hcore
    · calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [hx]; group
    · intro b hb
      have hb' : g * b * g⁻¹ ∈ Subgroup.normalizer (S : Set Y) := by
        rw [hN]
        exact ⟨b, hb, by simp⟩
      have := hc _ hb'
      calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [this]
        _ = b * (g⁻¹ * x * g) := by group
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem borelRigid_of_inner {Y : Type} [Group Y] [Finite Y]
    (hinn : K1.SylowCentralizingAutInner Y) (hZ : Subgroup.center Y = ⊥) {S₀ : Subgroup Y}
    (h₀ : IsSylowTwoOf S₀ ⊤)
    (hcore : ∀ x : Y, x * x = 1 → (∀ b ∈ Subgroup.normalizer (S₀ : Set Y), x * b = b * x) → x = 1) :
    BorelRigid Y := by
  intro S hS β hβ2 hβB
  have hSfix : ∀ s ∈ S, β s = s := fun s hs => hβB s (Subgroup.le_normalizer hs)
  obtain ⟨x, hx⟩ := hinn S hS β hSfix
  have hxx : x * x = 1 := by
    have hcen : x * x ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hβ2 y
      rw [hx, hx] at h1
      calc y * (x * x) = x * x * (x⁻¹ * (x⁻¹ * y * x) * x) := by group
        _ = x * x * y := by rw [h1]
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  have hxB : ∀ b ∈ Subgroup.normalizer (S : Set Y), x * b = b * x := by
    intro b hb
    have h1 := hβB b hb
    rw [hx] at h1
    calc x * b = x * (x⁻¹ * b * x) := by rw [h1]
      _ = b * x := by group
  have hx1 : x = 1 := core_of_sylow_conj h₀ hcore hS hxx hxB
  ext y
  rw [hx, hx1]
  simp

end Inner

end CFSG.Quasithin
