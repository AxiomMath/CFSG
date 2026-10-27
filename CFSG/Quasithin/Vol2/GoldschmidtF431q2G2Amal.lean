module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Set
public import CFSG.Quasithin.Background.F6CatInstancesG22Shape

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Shape

@[expose] noncomputable def restr {Y N : Type} [Group Y] [Group N] (ψ : Y ≃* N) {M : Subgroup Y}
    {K : Subgroup N} (h : M.map ψ.toMonoidHom = K) : ↥M ≃* ↥K :=
  (M.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr h)

theorem coe_restr {Y N : Type} [Group Y] [Group N] (ψ : Y ≃* N) {M : Subgroup Y}
    {K : Subgroup N} (h : M.map ψ.toMonoidHom = K) (m : ↥M) :
    ((restr ψ h m : ↥K) : N) = ψ m := rfl

theorem card_center_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card ↥(Subgroup.center X) = Nat.card ↥(Subgroup.center Y) := by
  rw [← Subgroup.map_center_eq e]
  exact Nat.card_congr ((Subgroup.center X).equivMapOfInjective e.toMonoidHom e.injective).toEquiv

namespace Model

open scoped Pointwise

variable {k : Type} [Field k] [Finite k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

theorem exists_psi {Y : Type} [Group Y] (ε : Y ≃* G2Group k) {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) :
    ∃ ψ : Y ≃* G2Group k,
      (M₁.map ψ.toMonoidHom = (lat h2 hk2).P₁ ∧ M₂.map ψ.toMonoidHom = (lat h2 hk2).P₂) ∨
        (M₁.map ψ.toMonoidHom = (lat h2 hk2).P₂ ∧ M₂.map ψ.toMonoidHom = (lat h2 hk2).P₁) := by
  have : Finite (G2Group k) := finite_g2Group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := IsYAmalgamPair.map ε hpair
  obtain ⟨-, hp', hidx'⟩ := hp.1
  have e1 : ((T.map ε.toMonoidHom).subgroupOf ⊤).index = (T.map ε.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have hidx : ¬ 2 ∣ (T.map ε.toMonoidHom).index := by rwa [e1] at hidx'
  let S : Sylow 2 (G2Group k) := (lat h2 hk2).sylow.1.toSylow (lat h2 hk2).sylow.2
  let S' : Sylow 2 (G2Group k) := hp'.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G2Group k) S S'
  have hg' : MulAut.conj g • (lat h2 hk2).S = T.map ε.toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 (G2Group k) => (P : Subgroup (G2Group k))) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hTmap : T.map ε.toMonoidHom = (lat h2 hk2).S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : G2Group k ≃* G2Group k := (MulAut.conj g).symm
  have hTφ : (T.map ε.toMonoidHom).map φ.toMonoidHom = (lat h2 hk2).S := by
    rw [hTmap]
    exact map_map_symm_eq (MulAut.conj g) (lat h2 hk2).S
  have hpair2 := IsYAmalgamPair.map φ hp
  rw [hTφ] at hpair2
  obtain ⟨-, hne, hiff⟩ := hpair2
  obtain ⟨hK₁, hN₁⟩ := (hiff _).2 (Or.inl rfl)
  obtain ⟨hK₂, hN₂⟩ := (hiff _).2 (Or.inr rfl)
  refine ⟨ε.trans φ, ?_⟩
  have hmap : ∀ M : Subgroup Y, M.map (ε.trans φ).toMonoidHom =
      (M.map ε.toMonoidHom).map φ.toMonoidHom := fun M => by
    rw [Subgroup.map_map]
    rfl
  rw [hmap M₁, hmap M₂]
  rcases (lat h2 hk2).eq_P₁_or_P₂_of_maxTwoLocal hK₁ (Subgroup.le_normalizer.trans hN₁) with
    h₁ | h₁ <;>
    rcases (lat h2 hk2).eq_P₁_or_P₂_of_maxTwoLocal hK₂ (Subgroup.le_normalizer.trans hN₂) with
      h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (h₁.trans h₂.symm) hne

include h2

theorem false_of_amalgam {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {H₁ H₂ : Subgroup G}
    {z : G} {Y : Type} [Group Y] (ε : Y ≃* G2Group k) {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂)
    (I : (RankTwoAmalgam.ofSubgroups H₁ H₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (hsp : IsSpecialPow 2 2 2 ↥(pCoreOf 2 H₁)) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hle1 : H₁ ≤ Subgroup.centralizer ({z} : Set G))
    (hle2 : Subgroup.centralizer ({z} : Set G) ≤ H₁) : False := by
  obtain ⟨f1, f12, f2, c1, c2⟩ : ∃ (f1 : ↥H₁ ≃* ↥M₁) (f12 : ↥(H₁ ⊓ H₂) ≃* ↥(M₁ ⊓ M₂))
      (f2 : ↥H₂ ≃* ↥M₂), (∀ x : ↥(H₁ ⊓ H₂), Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁)
        (f12 x) = f1 (Subgroup.inclusion (inf_le_left : H₁ ⊓ H₂ ≤ H₁) x)) ∧
      (∀ x : ↥(H₁ ⊓ H₂), Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) (f12 x) =
        f2 (Subgroup.inclusion (inf_le_right : H₁ ⊓ H₂ ≤ H₂) x)) :=
    ⟨I.φ1, I.φ12, I.φ2, I.comm1, I.comm2⟩
  obtain ⟨ψ, hψ⟩ := exists_psi h2 hk2 ε hpair
  rcases hψ with ⟨hM₁, hM₂⟩ | ⟨hM₁, hM₂⟩
  · let e : ↥H₁ ≃* ↥(lat h2 hk2).P₁ := f1.trans (restr ψ hM₁)
    have hcard : Nat.card ↥(pCoreOf 2 (lat h2 hk2).P₁) = 32 := by
      rw [← Nat.card_congr (pCoreOfCongr e).toEquiv, hsp.2.1]
      norm_num
    have hR := R1_eq_pCoreOf h2 hk2 hcard.le
    refine card_center_R1_ne h2 hk2 ?_
    rw [card_center_congr (MulEquiv.subgroupCongr hR), card_center_congr (pCoreOfCongr e).symm]
    exact hsp.2.2
  · have hSM : (M₁ ⊓ M₂).map ψ.toMonoidHom = (lat h2 hk2).S := by
      rw [Subgroup.map_inf _ _ _ ψ.injective, hM₁, hM₂, inf_comm, lattice_inf_eq]
    let e₁ : ↥H₁ ≃* ↥(lat h2 hk2).P₂ := f1.trans (restr ψ hM₁)
    let e₂ : ↥H₂ ≃* ↥(lat h2 hk2).P₁ := f2.trans (restr ψ hM₂)
    let φ₁ : ↥(lat h2 hk2).P₂ →* G := H₁.subtype.comp e₁.symm.toMonoidHom
    let φ₂ : ↥(lat h2 hk2).P₁ →* G := H₂.subtype.comp e₂.symm.toMonoidHom
    refine false_of_embeddings h2 hk2 φ₁ φ₂ (H₁.subtype_injective.comp e₁.symm.injective) ?_ ?_
      hz1 hz2
    · ext g
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨p, rfl⟩
        exact hle1 (e₁.symm p).2
      · intro hg
        exact ⟨e₁ ⟨g, hle2 hg⟩, by simp [φ₁]⟩
    · intro g h₁ h₂ hgS
      have hgM : ψ.symm g ∈ M₁ ⊓ M₂ := by
        rw [← hSM] at hgS
        obtain ⟨m, hm, hmg⟩ := hgS
        have : ψ.symm g = m := (MulEquiv.symm_apply_eq ψ).2 hmg.symm
        rw [this]
        exact hm
      set t : ↥(H₁ ⊓ H₂) := f12.symm ⟨ψ.symm g, hgM⟩ with ht
      have hφ12 : f12 t = ⟨ψ.symm g, hgM⟩ := f12.apply_symm_apply _
      have k1 : e₁ (Subgroup.inclusion (inf_le_left : H₁ ⊓ H₂ ≤ H₁) t) = ⟨g, h₂⟩ := by
        apply Subtype.ext
        show ((restr ψ hM₁ (f1 (Subgroup.inclusion (inf_le_left : H₁ ⊓ H₂ ≤ H₁) t)) :
          ↥(lat h2 hk2).P₂) : G2Group k) = g
        rw [coe_restr, ← c1, hφ12]
        exact ψ.apply_symm_apply g
      have k2 : e₂ (Subgroup.inclusion (inf_le_right : H₁ ⊓ H₂ ≤ H₂) t) = ⟨g, h₁⟩ := by
        apply Subtype.ext
        show ((restr ψ hM₂ (f2 (Subgroup.inclusion (inf_le_right : H₁ ⊓ H₂ ≤ H₂) t)) :
          ↥(lat h2 hk2).P₁) : G2Group k) = g
        rw [coe_restr, ← c2, hφ12]
        exact ψ.apply_symm_apply g
      have r1 : φ₁ ⟨g, h₂⟩ = ((t : ↥(H₁ ⊓ H₂)) : G) := by
        have : e₁.symm ⟨g, h₂⟩ = Subgroup.inclusion (inf_le_left : H₁ ⊓ H₂ ≤ H₁) t :=
          (MulEquiv.symm_apply_eq e₁).2 k1.symm
        change ((e₁.symm ⟨g, h₂⟩ : ↥H₁) : G) = _
        rw [this]
        rfl
      have r2 : φ₂ ⟨g, h₁⟩ = ((t : ↥(H₁ ⊓ H₂)) : G) := by
        have : e₂.symm ⟨g, h₁⟩ = Subgroup.inclusion (inf_le_right : H₁ ⊓ H₂ ≤ H₂) t :=
          (MulEquiv.symm_apply_eq e₂).2 k2.symm
        change ((e₂.symm ⟨g, h₁⟩ : ↥H₂) : G) = _
        rw [this]
        rfl
      rw [r1, r2]

end Model

end CFSG.Quasithin.H13.F431.G2Two
