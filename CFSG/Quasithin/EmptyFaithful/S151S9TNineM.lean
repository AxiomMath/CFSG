module

public import CFSG.Quasithin.EmptyFaithful.S151S9TNine
public import CFSG.Quasithin.EmptyFaithful.S151S9TModel

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def NineData (Γ : Type) [Group Γ] [Finite Γ] (S₀ Y₁ Y₆ P₀ : Subgroup Γ) : Prop :=
  IsSylowTwoOf S₀ ⊤ ∧ S₀ ≤ Y₁ ∧ S₀ ≤ Y₆ ∧ Y₁ ≤ P₀ ∧ Y₆ ≤ P₀ ∧ Y₁ ≠ Y₆ ∧ Y₁ ⊔ Y₆ = P₀ ∧
  Nat.card ↥Y₁ = 3 * Nat.card ↥S₀ ∧ Nat.card ↥Y₆ = 3 * Nat.card ↥S₀ ∧
  Nat.card ↥P₀ = 9 * Nat.card ↥S₀ ∧
  (∀ K : Subgroup Γ, S₀ ≤ K → K ≤ P₀ → K = S₀ ∨ K = Y₁ ∨ K = Y₆ ∨ K = P₀) ∧
  (∃ z₀ : Γ, orderOf z₀ = 2 ∧ centerOf S₀ = Subgroup.zpowers z₀ ∧
    ¬ P₀ ≤ Subgroup.centralizer ({z₀} : Set Γ)) ∧
  ¬ Y₁ ≤ Subgroup.normalizer (S₀ : Set Γ) ∧
  (∃ x₁ ∈ Y₁, ∃ x₆ ∈ Y₆, orderOf x₁ = 3 ∧ orderOf x₆ = 3 ∧ x₁ * x₆ = x₆ * x₁ ∧
    ∃ r : Fin 5 → Γ, (∀ i, ∀ a b : Fin 3,
      (x₁ ^ (a : ℕ) * x₆ ^ (b : ℕ))⁻¹ * r i * (x₁ ^ (a : ℕ) * x₆ ^ (b : ℕ)) ∈ S₀) ∧
      ∀ f : Γ, f ∈ ({x₁, x₆, x₁ * x₆, x₁ * x₆⁻¹} : Set Γ) →
        Function.Injective fun i => ⁅⁅r i, f⁆, f⁆) ∧
  (∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ →
    Y₁.map α.toMonoidHom = Y₁ ∨ Y₁.map α.toMonoidHom = Y₆)

namespace NineM

section Transport

variable {G : Type} [Group G] {L S : Subgroup G} {Γ : Type} [Group Γ]

theorem pullG_eq_map (e : ↥L ≃* Γ) (X : Subgroup Γ) :
    pullG e X = X.map (L.subtype.comp e.symm.toMonoidHom) :=
  Subgroup.map_map _ _ _

theorem injective_embed (e : ↥L ≃* Γ) :
    Function.Injective (L.subtype.comp e.symm.toMonoidHom) :=
  L.subtype_injective.comp e.symm.injective

theorem pullG_eq_inf (e : ↥L ≃* Γ) {S₀ : Subgroup Γ}
    (he : ((S ⊓ L).subgroupOf L).map e.toMonoidHom = S₀) : pullG e S₀ = S ⊓ L := by
  rw [← he]
  exact E2P.pull_map e inf_le_right

theorem not_pullG_le_centralizer {z : G} (hz : z ∈ centerOf (S ⊓ L))
    (hnc : ¬ L ≤ Subgroup.centralizer ({z} : Set G)) (e : ↥L ≃* Γ) {S₀ P₀ : Subgroup Γ}
    (he : ((S ⊓ L).subgroupOf L).map e.toMonoidHom = S₀) {z₀ : Γ} (hz₀o : orderOf z₀ = 2)
    (hz₀c : centerOf S₀ = Subgroup.zpowers z₀)
    (hz₀nc : ¬ P₀ ≤ Subgroup.centralizer ({z₀} : Set Γ)) :
    ¬ pullG e P₀ ≤ Subgroup.centralizer ({z} : Set G) := by
  set ι : Γ →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := injective_embed e
  have hSι : S₀.map ι = S ⊓ L := by
    rw [← pullG_eq_inf e he]
    exact (pullG_eq_map e S₀).symm
  have hmemP : ∀ c ∈ P₀, ι c ∈ pullG e P₀ := fun c hc => by
    rw [pullG_eq_map e P₀]
    exact Subgroup.mem_map_of_mem ι hc
  obtain ⟨w, rfl⟩ : ∃ w : Γ, ι w = z := ⟨e ⟨z, hz.1.2⟩, by simp [ι]⟩
  have hz1 : ι w ≠ 1 := by
    intro h
    apply hnc
    rw [h]
    intro l _
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      simp
  have hw1 : w ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hwc : w ∈ centerOf S₀ := by
    rw [← hSι] at hz
    exact (mem_centerOf_map_iff_of_injective hι).mp hz
  have hwz₀ : w = z₀ := eq_of_mem_centerOf_of_orderOf_two hz₀o hz₀c hwc hw1
  intro hP
  apply hz₀nc
  intro c hc
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  rw [Set.mem_singleton_iff] at hy
  have h1 := Subgroup.mem_centralizer_iff.mp (hP (hmemP c hc)) (ι w) rfl
  rw [hy, ← hwz₀]
  exact hι (by rw [map_mul, map_mul]; exact h1)

theorem conj_pullG_mem (hSN : S ≤ Subgroup.normalizer (L : Set G)) (e : ↥L ≃* Γ)
    {S₀ Y₁ Y₆ : Subgroup Γ} (he : ((S ⊓ L).subgroupOf L).map e.toMonoidHom = S₀)
    (hinv : ∀ α : MulAut Γ, S₀.map α.toMonoidHom = S₀ →
      Y₁.map α.toMonoidHom = Y₁ ∨ Y₁.map α.toMonoidHom = Y₆) {t : G} (ht : t ∈ S) :
    (pullG e Y₁).map (MulAut.conj t).toMonoidHom = pullG e Y₁ ∨
      (pullG e Y₁).map (MulAut.conj t).toMonoidHom = pullG e Y₆ := by
  rw [map_conj_pullG e (hSN ht) Y₁]
  rcases hinv _ (map_autN_eq_of_mem e he (hSN ht) ht) with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

theorem normalizes_sup_of_conj_mem {Y₁ Y₆ : Subgroup G} (hne : Y₁ ≠ Y₆)
    (hperm : ∀ t ∈ S, Y₁.map (MulAut.conj t).toMonoidHom = Y₁ ∨
      Y₁.map (MulAut.conj t).toMonoidHom = Y₆)
    (hswap : ¬ S ≤ Subgroup.normalizer (Y₁ : Set G)) :
    S ≤ Subgroup.normalizer ((Y₁ ⊔ Y₆ : Subgroup G) : Set G) := by
  obtain ⟨t', ht'S, ht'⟩ := IsConcreteLE.not_le_iff_exists.mp hswap
  have ht'6 : Y₁.map (MulAut.conj t').toMonoidHom = Y₆ := by
    rcases hperm t' ht'S with h | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h) ht'
    · exact h
  intro t ht
  have hinjc : Function.Injective fun X : Subgroup G => X.map (MulAut.conj t).toMonoidHom :=
    fun X Y h => Subgroup.map_injective (MulAut.conj t).injective h
  have h6 : Y₆.map (MulAut.conj t).toMonoidHom = Y₁ ∨ Y₆.map (MulAut.conj t).toMonoidHom = Y₆ := by
    have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t').toMonoidHom =
        (MulAut.conj (t * t')).toMonoidHom := by
      ext x
      simp [mul_assoc]
    have h := hperm (t * t') (S.mul_mem ht ht'S)
    have h' : (Y₁.map (MulAut.conj t').toMonoidHom).map (MulAut.conj t).toMonoidHom =
        Y₁.map (MulAut.conj (t * t')).toMonoidHom := by
      rw [Subgroup.map_map, hcomp]
    rw [ht'6] at h'
    rw [h']
    exact h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Y₁ ⊔ Y₆).map (MulAut.conj t).toMonoidHom = Y₁ ⊔ Y₆
  rw [Subgroup.map_sup]
  rcases hperm t ht with h1 | h1 <;> rcases h6 with h2 | h2
  · exact absurd (hinjc (h1.trans h2.symm)) hne
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]
  · exact absurd (hinjc (h1.trans h2.symm)) hne

end Transport

end NineM

theorem threeD_of_pull_nine {G : Type} [Group G] [Finite G] {L S : Subgroup G} {z : G}
    (hS2 : IsPGroup 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hz : z ∈ centerOf (S ⊓ L))
    (hnc : ¬ L ≤ Subgroup.centralizer ({z} : Set G))
    {Γ : Type} [Group Γ] [Finite Γ] (e : ↥L ≃* Γ) {S₀ Y₁ Y₆ P₀ : Subgroup Γ}
    (he : ((S ⊓ L).subgroupOf L).map e.toMonoidHom = S₀) (hM : NineData Γ S₀ Y₁ Y₆ P₀)
    (hswap : ¬ S ≤ Subgroup.normalizer ((pullG e Y₁ : Subgroup G) : Set G)) :
    pullG e P₀ ≤ L ∧ S ⊓ L ≤ pullG e P₀ ∧
      S ≤ Subgroup.normalizer ((pullG e P₀ : Subgroup G) : Set G) ∧
      ¬ pullG e P₀ ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo (pullG e P₀) ∧
      IsMinParabolicOf (pullG e P₀ ⊔ S) (pullG e P₀ ⊔ S) ∧ NumC126 (pullG e P₀ ⊔ S) ∧
      oPrimeResidualOf 3 (pullG e P₀) ⊔ (S ⊓ L) = pullG e P₀ := by
  obtain ⟨-, hSY₁, hSY₆, hY₁P, hY₆P, hne, hsup, hc₁, hc₆, hcP, hlat₀, ⟨z₀, hz₀o, hz₀c, hz₀nc⟩,
    hnN₀, ⟨x₁, hx₁, x₆, hx₆, hx₁o, hx₆o, hcomm, r, hr, hrinj⟩, hinv⟩ := hM
  set ι : Γ →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := NineM.injective_embed e
  have hpull : ∀ X : Subgroup Γ, pullG e X = X.map ι := NineM.pullG_eq_map e
  have hpS : pullG e S₀ = S ⊓ L := NineM.pullG_eq_inf e he
  have hSι : S₀.map ι = S ⊓ L := by rw [← hpull]; exact hpS
  have hmem : ∀ X : Subgroup Γ, ∀ c ∈ X, ι c ∈ pullG e X := fun X c hc => by
    rw [hpull]
    exact Subgroup.mem_map_of_mem ι hc
  have hmemS : ∀ c ∈ S₀, ι c ∈ S ⊓ L := fun c hc => hpS ▸ hmem S₀ c hc
  have hcard : ∀ X : Subgroup Γ, Nat.card ↥(pullG e X) = Nat.card ↥X := fun X => by
    rw [hpull]
    exact Subgroup.card_map_of_injective hι
  have hcS : Nat.card ↥(S ⊓ L) = Nat.card ↥S₀ := by
    rw [← hpS]
    exact hcard S₀
  have hPL : pullG e P₀ ≤ L := E2P.pull_le e P₀
  have hBP : S ⊓ L ≤ pullG e P₀ := hpS ▸ E2P.pull_mono e (hSY₁.trans hY₁P)
  have hBY₁ : S ⊓ L ≤ pullG e Y₁ := hpS ▸ E2P.pull_mono e hSY₁
  have hBY₆ : S ⊓ L ≤ pullG e Y₆ := hpS ▸ E2P.pull_mono e hSY₆
  have hlat : ∀ K : Subgroup G, S ⊓ L ≤ K → K ≤ pullG e P₀ →
      K = S ⊓ L ∨ K = pullG e Y₁ ∨ K = pullG e Y₆ ∨ K = pullG e P₀ := by
    intro K hBK hKP
    have hKL : K ≤ L := hKP.trans hPL
    have hKK₀ : pullG e ((K.subgroupOf L).map e.toMonoidHom) = K := E2P.pull_map e hKL
    have hBK' : S ⊓ L ≤ pullG e ((K.subgroupOf L).map e.toMonoidHom) := by
      rw [hKK₀]
      exact hBK
    have h1 : S₀ ≤ (K.subgroupOf L).map e.toMonoidHom := by
      have h := (E2P.le_pull_iff e (inf_le_right : S ⊓ L ≤ L)
        (P := (K.subgroupOf L).map e.toMonoidHom)).mp hBK'
      rwa [he] at h
    have h2 : (K.subgroupOf L).map e.toMonoidHom ≤ P₀ := (E2P.le_pull_iff e hKL).mp hKP
    rcases hlat₀ _ h1 h2 with h | h | h | h
    · exact Or.inl (by rw [← hKK₀, h, hpS])
    · exact Or.inr (Or.inl (by rw [← hKK₀, h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [← hKK₀, h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [← hKK₀, h])))
  have hne' : pullG e Y₁ ≠ pullG e Y₆ := fun h => hne (pullG_injective e h)
  have hsup' : pullG e Y₁ ⊔ pullG e Y₆ = pullG e P₀ := by
    rw [← hsup, hpull, hpull, hpull, Subgroup.map_sup]
  have hSP : S ≤ Subgroup.normalizer ((pullG e P₀ : Subgroup G) : Set G) := by
    rw [← hsup']
    exact NineM.normalizes_sup_of_conj_mem hne'
      (fun t ht => NineM.conj_pullG_mem hSN e he hinv ht) hswap
  have hPz : ¬ pullG e P₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    NineM.not_pullG_le_centralizer hz hnc e he hz₀o hz₀c hz₀nc
  have hnN : ¬ pullG e Y₁ ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro hY
    apply hnN₀
    intro c hc
    have h1 := hY (hmem Y₁ c hc)
    rw [← hSι] at h1
    exact (E2P.mem_normalizer_map_iff_of_injective hι).mp h1
  have hswap' : ∃ t ∈ S, t ∉ Subgroup.normalizer ((pullG e Y₁ : Subgroup G) : Set G) :=
    IsConcreteLE.not_le_iff_exists.mp hswap
  have hrE : ∀ i, ∀ a b : Fin 3,
      ((ι x₁) ^ (a : ℕ) * (ι x₆) ^ (b : ℕ))⁻¹ * ι (r i) * ((ι x₁) ^ (a : ℕ) * (ι x₆) ^ (b : ℕ)) ∈
        S ⊓ L := fun i a b => by
    have h := hmemS _ (hr i a b)
    rwa [map_mul, map_mul, map_inv, map_mul, map_pow, map_pow] at h
  have hinj : ∀ f : G, f ∈ ({ι x₁, ι x₆, ι x₁ * ι x₆, ι x₁ * (ι x₆)⁻¹} : Set G) →
      Function.Injective fun i => ⁅⁅ι (r i), f⁆, f⁆ := by
    have key : ∀ f₀ : Γ, f₀ ∈ ({x₁, x₆, x₁ * x₆, x₁ * x₆⁻¹} : Set Γ) →
        Function.Injective fun i => ⁅⁅ι (r i), ι f₀⁆, ι f₀⁆ := by
      intro f₀ hf₀ i j h
      apply hrinj f₀ hf₀
      apply hι
      simpa only [map_commutatorElement] using h
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact key x₁ (by simp)
    · exact key x₆ (by simp)
    · simpa only [map_mul] using key (x₁ * x₆) (by simp)
    · simpa only [map_mul, map_inv] using key (x₁ * x₆⁻¹) (by simp)
  obtain ⟨hchar, hmin, hnum, hoP⟩ := idx9_core (L := L) (S := S) (P := pullG e P₀)
    (Y₁ := pullG e Y₁) (Y₆ := pullG e Y₆) hS2 hSN hPL hSP hBY₁ hBY₆ (E2P.pull_mono e hY₁P)
    (E2P.pull_mono e hY₆P) hne' hsup' (by rw [hcard, hc₁, hcS]) (by rw [hcard, hc₆, hcS])
    (by rw [hcard, hcP, hcS]) hlat hnN hswap' (hmem Y₁ x₁ hx₁) (hmem Y₆ x₆ hx₆)
    (by rw [orderOf_injective ι hι, hx₁o]) (by rw [orderOf_injective ι hι, hx₆o])
    (by rw [← map_mul, ← map_mul, hcomm]) hrE hinj
  exact ⟨hPL, hBP, hSP, hPz, hchar, hmin, hnum, hoP⟩

end CFSG.Quasithin.S151S9T
