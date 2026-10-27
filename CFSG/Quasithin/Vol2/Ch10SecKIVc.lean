module

public import CFSG.Quasithin.Vol2.Ch10SecKIVb
public import CFSG.Quasithin.Background.A312SporJ1
public import Certificates.Certificate3119
public import Certificates.Certificate7124
public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.A312S CFSG.Quasithin.E2P.SporB CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.J1


theorem j1_overgroup_card {Z : Subgroup ↥J} (hSZ : j1S ≤ Z) (h60 : 60 ∣ Nat.card Z) :
    Z = ⊤ ∨ Nat.card Z = 120 := by
  obtain ⟨j, hj, hZ⟩ := j1_all Z hSZ
  have hsize : (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ).size =
      17 := rfl
  rw [hsize] at hj hZ
  by_cases hj17 : j < 17
  · right
    rw [memberOrTop, ite_eq_left hj17] at hZ
    subst hZ
    rw [j1_Y_card hj17] at h60 ⊢
    have key : ∀ i < 17,
        60 ∣ (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[i]! * 2 ^ 3 →
        (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[i]! * 2 ^ 3 =
          120 := by
      decide
    exact key j hj17 h60
  · left
    rw [memberOrTop, ite_eq_right hj17] at hZ
    exact hZ

theorem j1_isQuasisimple : CFSG.IsQuasisimple ↥J := by
  have := isSimpleGroup_J
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  have hn : (j1S).Normal := ⟨fun n hn g => by
    rw [h g n, mul_inv_cancel_right]
    exact hn⟩
  have hc : Nat.card ↥j1S = 8 := by
    have h := j1_Y_card (j := 0) (by norm_num)
    rw [j1_Y_zero] at h
    exact h.trans (by decide)
  rcases Subgroup.Normal.eq_bot_or_eq_top j1S with h1 | h1
  · rw [h1, Subgroup.card_bot] at hc
    norm_num at hc
  · rw [h1, Subgroup.card_top, card_J] at hc
    norm_num at hc

theorem j1_card_sup_of_mem {B : Subgroup ↥J} (hB : B ∈ lFamily j1S) (h : IsAlt 5 ↥B) :
    Nat.card ↥(B ⊔ j1S) = 120 := by
  have c := card_eq_sixty h
  have h60 : 60 ∣ Nat.card ↥(B ⊔ j1S) := by
    rw [← c]
    exact Subgroup.card_dvd_of_le le_sup_left
  rcases j1_overgroup_card (le_sup_right : j1S ≤ B ⊔ j1S) h60 with htop | h120
  · exfalso
    have hB' : B ∈ cComp (B ⊔ j1S) := hB
    rw [htop] at hB'
    rw [A321.cComp_eq_top_of_quasisimple j1_isQuasisimple hB', Subgroup.card_top, card_J] at c
    norm_num at c
  · exact h120

theorem j1_le_normalizer {B : Subgroup ↥J} (hB : B ∈ lFamily j1S) (h : IsAlt 5 ↥B) :
    j1S ≤ Subgroup.normalizer (B : Set ↥J) := by
  have c := card_eq_sixty h
  have hs := j1_card_sup_of_mem hB h
  have hidx : (B.subgroupOf (B ⊔ j1S)).index = 2 := by
    have hm := Subgroup.relIndex_mul_card (H := B) (K := B ⊔ j1S)
    rw [inf_of_le_left le_sup_left, c, hs] at hm
    change B.relIndex (B ⊔ j1S) = 2
    omega
  have := Subgroup.normal_of_index_eq_two hidx
  exact le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp this)

theorem j1_sup_eq_top {B₁ B₂ : Subgroup ↥J} (hB₁ : B₁ ∈ lFamily j1S)
    (hB₂ : B₂ ∈ lFamily j1S) (h₁ : IsAlt 5 ↥B₁) (h₂ : IsAlt 5 ↥B₂) (hne : B₁ ≠ B₂) :
    B₁ ⊔ B₂ = ⊤ := by
  have := isSimpleGroup_J
  have c₁ := card_eq_sixty h₁
  have c₂ := card_eq_sixty h₂
  have := isSimpleGroup_of_isAlt h₁
  have hN : j1S ≤ Subgroup.normalizer ((B₁ ⊔ B₂ : Subgroup ↥J) : Set ↥J) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (j1_le_normalizer hB₁ h₁ hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (j1_le_normalizer hB₂ h₂ hg)]
  have h60 : 60 ∣ Nat.card ↥((B₁ ⊔ B₂) ⊔ j1S) := by
    rw [← c₁]
    exact Subgroup.card_dvd_of_le (le_sup_left.trans le_sup_left)
  rcases j1_overgroup_card (le_sup_right : j1S ≤ (B₁ ⊔ B₂) ⊔ j1S) h60 with htop | h120
  · have hn : (B₁ ⊔ B₂).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      exact sup_le Subgroup.le_normalizer hN
    rcases Subgroup.Normal.eq_bot_or_eq_top (B₁ ⊔ B₂) with h | h
    · exfalso
      have hB : B₁ = ⊥ := le_bot_iff.mp (h ▸ le_sup_left)
      rw [hB, Subgroup.card_bot] at c₁
      norm_num at c₁
    · exact h
  · exfalso
    have hd : Nat.card ↥(B₁ ⊔ B₂) ∣ 120 := by
      rw [← h120]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hd' : 60 ∣ Nat.card ↥(B₁ ⊔ B₂) := by
      rw [← c₁]
      exact Subgroup.card_dvd_of_le le_sup_left
    obtain ⟨k, hk⟩ := hd'
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < Nat.card ↥(B₁ ⊔ B₂) := Nat.card_pos
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · exact hne (eq_of_card_sup_eq (by rw [hk, c₁]) (by rw [hk, c₂]))
    · exact hne (eq_of_card_sup_eq_double (by norm_num) c₁ c₂ (by rw [hk]))

theorem sup_eq_top_J1 {Y : Type} [Group Y] [Finite Y] (hY : IsSporadic .J1 Y) {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) {B₁ B₂ : Subgroup Y} (hB₁ : B₁ ∈ lFamily T) (hB₂ : B₂ ∈ lFamily T)
    (h₁ : IsAlt 5 ↥B₁) (h₂ : IsAlt 5 ↥B₂) (hne : B₁ ≠ B₂) : B₁ ⊔ B₂ = ⊤ := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* ↥J := e₀.trans nativeEquiv
  have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hT
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf j1_sylow hT'
  let φ : Y ≃* ↥J := e.trans (MulAut.conj g).symm
  have hTφ : T.map φ.toMonoidHom = j1S := by
    have h1 : T.map φ.toMonoidHom =
        (T.map e.toMonoidHom).map (MulAut.conj g).symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, ← hg, Vol2Native.A312L.map_map_symm]
  have hmem : ∀ {B : Subgroup Y}, B ∈ lFamily T → B.map φ.toMonoidHom ∈ lFamily j1S :=
    fun {B} hB => by
      have h1 := cComp_map_mulEquiv φ (show B ∈ cComp (B ⊔ T) from hB)
      rw [Subgroup.map_sup, hTφ] at h1
      exact h1
  have halt : ∀ {B : Subgroup Y}, IsAlt 5 ↥B → IsAlt 5 ↥(B.map φ.toMonoidHom) :=
    fun {B} ⟨a⟩ => ⟨(B.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans a⟩
  have hne' : B₁.map φ.toMonoidHom ≠ B₂.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have h := j1_sup_eq_top (hmem hB₁) (hmem hB₂) (halt h₁) (halt h₂) hne'
  rw [← Subgroup.map_sup] at h
  exact eq_top_of_map_eq_top φ h

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV
