module

public import CFSG.Quasithin.Vol2.Ch6OrthX
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOSL

public section

namespace CFSG.Quasithin.H13.L216

open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)
open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {F : Type} [Field F]

@[expose] noncomputable def coordHom (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) : ↥L →* SL(2, F) :=
  ψ.toMonoidHom.comp (autHom hLV)

theorem coordHom_apply (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) (ℓ : ↥L) :
    coordHom hLV ψ ℓ = ψ (autHom hLV ℓ) := rfl

theorem coordHom_eq_one_iff (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) (ℓ : ↥L) :
    coordHom hLV ψ ℓ = 1 ↔ (ℓ : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    have h1 : autHom hLV ℓ = 1 := by
      apply ψ.injective
      rw [coordHom_apply] at h
      rw [h, map_one]
    exact mem_centralizer_of_autHom_eq_one hLV h1
  · intro h
    have h1 : autHom hLV ℓ = 1 := by
      apply Subtype.ext
      exact (conjAct_eq_one_iff_ch6 (W := V) ⟨(ℓ : G), hLV ℓ.2⟩).mpr h
    rw [coordHom_apply, h1, map_one]

theorem coordHom_mem_U0_iff (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T) (ℓ : ↥L) :
    (∃ b : F, coordHom hLV ψ ℓ = unipSL b) ↔ (ℓ : G) ∈ T := by
  constructor
  · rintro ⟨b, hb⟩
    have hmem : (autHom hLV ℓ : MulAut V) ∈ autOn (T ⊓ L) V :=
      (hψ (autHom hLV ℓ)).mpr ⟨b, hb⟩
    exact mem_of_conjAct_mem_autOn hC ⟨(ℓ : G), hLV ℓ.2⟩ ((le_sup_left : L ≤ L ⊔ T) ℓ.2) hmem
  · intro hℓT
    have hmem : (autHom hLV ℓ : MulAut V) ∈ autOn (T ⊓ L) V :=
      AutOn.conjAct_mem_autOn_of_mem (hLV ℓ.2) ⟨hℓT, ℓ.2⟩
    obtain ⟨b, hb⟩ := (hψ (autHom hLV ℓ)).mp hmem
    exact ⟨b, hb⟩

theorem coordHom_ker_mem (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T) (ℓ : ↥L)
    (h : coordHom hLV ψ ℓ = 1) : (ℓ : G) ∈ T ⊓ L :=
  ⟨(coordHom_mem_U0_iff hLV ψ hψ hC ℓ).mp ⟨0, by
    rw [h]
    exact (CFSG.Quasithin.Vol2.Ch10.SecA.unipSL_zero (F := F)).symm⟩, ℓ.2⟩

theorem coordHom_mem_U0 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T) (ℓ : ↥L) (hℓ : (ℓ : G) ∈ T) :
    coordHom hLV ψ ℓ ∈ CFSG.PSL2Table.unipSL F :=
  (CFSG.PSL2Table.mem_unipSL_iff _).mpr (by
    obtain ⟨b, hb⟩ := (coordHom_mem_U0_iff hLV ψ hψ hC ℓ).mpr hℓ
    rw [hb, coe_unipSL]
    simp)

theorem coordHom_surjective (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F)) : Function.Surjective (coordHom hLV ψ) := by
  intro g
  obtain ⟨x, hx⟩ := ψ.surjective g
  obtain ⟨n, hn, hxn⟩ := AutOn.mem_autOn_iff.mp x.2
  refine ⟨⟨(n : G), hn⟩, ?_⟩
  rw [coordHom_apply]
  have : autHom hLV ⟨(n : G), hn⟩ = x := Subtype.ext hxn
  rw [this, hx]

theorem exists_of_mem_U0 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T) {g : SL(2, F)}
    (hg : g ∈ CFSG.PSL2Table.unipSL F) :
    ∃ ℓ : ↥L, (ℓ : G) ∈ T ⊓ L ∧ coordHom hLV ψ ℓ = g := by
  obtain ⟨b, rfl⟩ := (mem_U0_iff g).mp hg
  obtain ⟨ℓ, hℓ⟩ := coordHom_surjective hLV ψ (unipSL b)
  exact ⟨ℓ, ⟨(coordHom_mem_U0_iff hLV ψ hψ hC ℓ).mp ⟨b, hℓ⟩, ℓ.2⟩, hℓ⟩

theorem coordHom_upper (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (ℓ : ↥L) (hℓ : (ℓ : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    (coordHom hLV ψ ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hN : (autHom hLV ℓ : MulAut V) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V)) :=
    conjAct_mem_normalizer_autOn ⟨(ℓ : G), hLV ℓ.2⟩ hℓ
  have := upper_of_mem_normalizer ψ hψ (autHom hLV ℓ) hN
  rw [coordHom_apply]
  exact this

end CFSG.Quasithin.H13.L216
