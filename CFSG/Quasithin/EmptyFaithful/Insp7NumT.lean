module

public import CFSG.Quasithin.EmptyFaithful.Insp7Final3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Insp7

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem card_centralizer_dvd {L Gc : Type} [Group L] [Finite L] [Group Gc] [Finite Gc]
    (hZ : Subgroup.center L = ⊥) (ρ : Gc →* MulAut L) (hρ : Function.Injective ρ)
    (hinn : ∀ l : L, MulAut.conj l ∈ ρ.range) (z : L) (ž : Gc) (hž : ρ ž = MulAut.conj z) :
    Nat.card (Subgroup.centralizer ({ž} : Set Gc)) ∣
      Nat.card (Subgroup.centralizer ({z} : Set L)) * Nat.card (Outer L) := by
  set C : Subgroup Gc := Subgroup.centralizer ({ž} : Set Gc) with hC
  set H : Subgroup Gc := (Inn L).comap ρ with hH
  have hHn : H.Normal := Subgroup.normal_comap ρ
  set B : Subgroup Gc := H ⊓ C with hB
  have hBC : B ≤ C := inf_le_right
  have hCB : Nat.card C = Nat.card B * B.relIndex C := by
    have h1 := Subgroup.card_mul_index (B.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv] at h1
    exact h1.symm
  have hrel : B.relIndex C ∣ Nat.card (Outer L) := by
    have h1 : B.relIndex C = H.relIndex C := Subgroup.inf_relIndex_right H C
    have h2 : H.relIndex C ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H C
    have h3 : H.index = (Inn L).relIndex ρ.range := Subgroup.index_comap (Inn L) ρ
    have hinn' : Inn L ≤ ρ.range := by
      rintro _ ⟨l, rfl⟩
      exact hinn l
    have h4 : (Inn L).relIndex ρ.range ∣ (Inn L).index :=
      Subgroup.relIndex_dvd_index_of_le hinn'
    have h5 : (Inn L).index = Nat.card (Outer L) := rfl
    rw [h1]
    exact h2.trans (h3 ▸ h4.trans (h5 ▸ dvd_rfl))
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conj_eq_center, hZ]
  let e1 : L ≃* (MulAut.conj : L →* MulAut L).range := MonoidHom.ofInjective hinj
  let ρB : B →* (MulAut.conj : L →* MulAut L).range :=
    (ρ.comp B.subtype).codRestrict _ (fun b => b.2.1)
  let κ : B →* L := (e1.symm : _ →* L).comp ρB
  have hκ : ∀ b : B, MulAut.conj (κ b) = ρ b := by
    intro b
    have h1 := congrArg Subtype.val (e1.apply_symm_apply (ρB b))
    exact h1
  have hκC : ∀ b : B, κ b ∈ Subgroup.centralizer ({z} : Set L) := by
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hb : (b : Gc) * ž = ž * b := Subgroup.mem_centralizer_singleton_iff.mp b.2.2
    apply hinj
    rw [map_mul, map_mul, hκ b, ← hž, ← map_mul, ← map_mul, hb]
  let κ' : B →* Subgroup.centralizer ({z} : Set L) := κ.codRestrict _ hκC
  have hκ'inj : Function.Injective κ' := by
    intro a b hab
    have h1 : κ a = κ b := congrArg Subtype.val hab
    apply Subtype.ext
    apply hρ
    rw [← hκ a, ← hκ b, h1]
  have hBdvd : Nat.card B ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) :=
    Subgroup.card_dvd_of_injective κ' hκ'inj
  rw [hCB]
  exact Nat.mul_dvd_mul hBdvd hrel

theorem card_outer_le {L : Type} [Group L] [Finite L] (hZ : Subgroup.center L = ⊥) {k : ℕ}
    (h : Nat.card (MulAut L) ≤ k * Nat.card L) : Nat.card (Outer L) ≤ k := by
  have h1 := Subgroup.card_mul_index (Inn L)
  have h2 : Nat.card (Inn L) = Nat.card L := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv |>.symm,
      ker_conj_eq_center, hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv
  have h3 : (Inn L).index = Nat.card (Outer L) := rfl
  rw [h2, h3] at h1
  have h4 : Nat.card L * Nat.card (Outer L) ≤ Nat.card L * k :=
    calc Nat.card L * Nat.card (Outer L) = Nat.card (MulAut L) := h1
      _ ≤ k * Nat.card L := h
      _ = Nat.card L * k := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h4 Nat.card_pos

theorem numFactAt_of_centralizer {F : ∀ (L : Type) [Group L], Prop} {k : ℕ} (S : Finset ℕ)
    (hS : ∀ c ∈ S, ∀ o ∈ Finset.Icc 1 k, ¬ 9 ∣ c * o)
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      Subgroup.center L = ⊥ ∧ Nat.card (MulAut L) ≤ k * Nat.card L ∧
        ∀ z : L, z * z = 1 → z ≠ 1 →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∈ S) :
    NumFactAt F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ _ _ _ _ hC9
  obtain ⟨hZ, hA, hcz⟩ := hF L hq hFL
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ Subgroup.one_mem _)
  have hdvd := card_centralizer_dvd hZ ρ hρ hinn z ž hž
  have hout := card_outer_le hZ hA
  have h9 : 9 ∣ Nat.card (Subgroup.centralizer ({ž} : Set Gc)) := ⟨Nat.card Ŝ, hC9⟩
  exact hS _ (hcz z hz2 hz1) (Nat.card (Outer L)) (Finset.mem_Icc.mpr ⟨Nat.card_pos, hout⟩)
    (h9.trans hdvd)

theorem numFactAt_of_model {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥) {k : ℕ}
    (hA : Nat.card (MulAut X) ≤ k * Nat.card X) (S : Finset ℕ)
    (hS : ∀ c ∈ S, ∀ o ∈ Finset.Icc 1 k, ¬ 9 ∣ c * o)
    (hc : ∀ t : X, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set X)) ∈ S) :
    NumFactAt (fun L _ => Nonempty (L ≃* X)) := by
  refine numFactAt_of_centralizer S hS (fun L _ _ _ ⟨e⟩ => ⟨?_, ?_, ?_⟩)
  · have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center X := Subgroup.map_center_eq e
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  · rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact hA
  · intro z hz2 hz1
    have hz2' : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
    have hz1' : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
    have hord : orderOf (e z) = 2 := orderOf_eq_prime (by rwa [sq]) hz1'
    have hcard : Nat.card (Subgroup.centralizer ({z} : Set L)) =
        Nat.card (Subgroup.centralizer ({e z} : Set X)) := by
      rw [← map_centralizer_singleton_mulEquiv e z]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
    rw [hcard]
    exact hc (e z) hord

end Insp7

end CFSG.Quasithin
