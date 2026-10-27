module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L34
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate2022
public import Certificates.Certificate5158

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Open

theorem g4_comm_r4 : g₄ * r₄ = r₄ * g₄ :=
  ((tabRep_g₄.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_g₄)).1 (by decide +kernel)

theorem g5_comm_r4 : g₅ * r₄ = r₄ * g₅ :=
  ((tabRep_g₅.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_g₅)).1 (by decide +kernel)

theorem g6_comm_r4 : g₆ * r₄ = r₄ * g₆ :=
  ((tabRep_g₆.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_g₆)).1 (by decide +kernel)

theorem comm_r4_mem_S {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) :
    c * r₄ * c⁻¹ * r₄⁻¹ ∈ S := by
  have hr4 : r₄ ∈ R := r₄_mem_R
  have hc1 : ∀ x ∈ S, ∀ d ∈ R, d * x * d⁻¹ ∈ S := fun x hx d hd => conj_mem_S hd hx
  refine Subgroup.closure_induction (p := fun c _ => c * r₄ * c⁻¹ * r₄⁻¹ ∈ S) ?_ ?_ ?_ ?_ hc
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · have := S.mul_mem g₁_mem_S (hc1 g₁⁻¹ (S.inv_mem g₁_mem_S) r₄ hr4)
      simpa [mul_assoc] using this
    · have := S.mul_mem g₂_mem_S (hc1 g₂⁻¹ (S.inv_mem g₂_mem_S) r₄ hr4)
      simpa [mul_assoc] using this
    · have := S.mul_mem g₃_mem_S (hc1 g₃⁻¹ (S.inv_mem g₃_mem_S) r₄ hr4)
      simpa [mul_assoc] using this
    · rw [mul_assoc, g4_comm_r4]; simp [mul_assoc]
    · rw [mul_assoc, g5_comm_r4]; simp [mul_assoc]
    · rw [mul_assoc, g6_comm_r4]; simp [mul_assoc]
  · simp
  · intro a b ha hb ih1 ih2
    have h1 : a * b * r₄ * (a * b)⁻¹ * r₄⁻¹ =
        (a * (b * r₄ * b⁻¹ * r₄⁻¹) * a⁻¹) * (a * r₄ * a⁻¹ * r₄⁻¹) := by group
    rw [h1]
    exact S.mul_mem (hc1 _ ih2 a ha) ih1
  · intro a ha ih
    have h1 : a⁻¹ * r₄ * a⁻¹⁻¹ * r₄⁻¹ = a⁻¹ * (a * r₄ * a⁻¹ * r₄⁻¹)⁻¹ * a⁻¹⁻¹ := by
      group
    rw [h1]
    exact hc1 _ (S.inv_mem ih) a⁻¹ (R.inv_mem ha)

private theorem w183finL34_exists_ne_one_ne {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {A : Subgroup G} (hcard : Nat.card A = 4) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) :
    ∃ y ∈ A, y ≠ 1 ∧ y ≠ x := by
  haveI : Fintype A := Fintype.ofFinite A
  have hcardA : Fintype.card A = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hne : (⟨1, A.one_mem⟩ : A) ≠ ⟨x, hxA⟩ := fun h => hx1 (congrArg Subtype.val h).symm
  have hs : ({⟨1, A.one_mem⟩, ⟨x, hxA⟩} : Finset A).card = 2 := Finset.card_pair hne
  obtain ⟨y, -, hy_notMem⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({⟨1, A.one_mem⟩, ⟨x, hxA⟩} : Finset A)) (t := Finset.univ) (by
      rw [Finset.card_univ, hs, hcardA]
      norm_num)
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · intro h
    exact hy_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Subtype.ext h))
  · intro h
    exact hy_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Subtype.ext h))

private theorem w183finL34_r4_mul_self : r₄ * r₄ = 1 := by
  have h := pow_orderOf_eq_one r₄R
  rw [orderOf_r₄R, pow_two] at h
  have h' : ((r₄R * r₄R : R) : Equiv.Perm (Fin 42)) = 1 := congrArg Subtype.val h
  rw [Subgroup.coe_mul] at h'
  exact h'

private theorem w183finL34_card_centralizer_inf_conj_r4
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({c * r₄ * c⁻¹} : Set (Equiv.Perm (Fin 42)))) = 72 := by
  rw [CFSG.GH74.GLS.IVK.l34_card_inf_centralizer_conj hc r₄]
  have h := card_C₄
  rw [show C₄ = Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ S from rfl,
    inf_comm] at h
  exact h

theorem card_centralizer_conj_r4 {c : Equiv.Perm (Fin 42)}
    (hc : c ∈ R) :
    Nat.card ↥(Subgroup.centralizer ({c * r₄ * c⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 := by
  rw [inf_comm]
  exact w183finL34_card_centralizer_inf_conj_r4 hc

private theorem w183finL34_card_centralizer_of_mem_S_involution
    {w : Equiv.Perm (Fin 42)} (hwS : w ∈ S) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 64 := by
  have hwR : w ∈ R := S_le_R hwS
  have hw2' : orderOf w = 2 := orderOf_eq_prime (by rwa [pow_two]) hw1
  rcases CFSG.GH74.GLS.IVK.l34_inv_cases hwR hw2' with
      ⟨c, hc, hce, hcard⟩ | ⟨c, hc, hce, hcard⟩ | ⟨c, hc, hce, hcard⟩ |
        ⟨c, hc, hce, hcard⟩
  · rwa [inf_comm]
  · exact absurd (conj_mem_S' hc (by rw [← hce]; exact hwS)) not_mem_S_r₂
  · exact absurd (conj_mem_S' hc (by rw [← hce]; exact hwS)) not_mem_S_r₃
  · exact absurd (conj_mem_S' hc (by rw [← hce]; exact hwS)) not_mem_S_r₄

theorem outer_class_r4
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAR : A ≤ R) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ S, g * t = t * g → ∀ a ∈ A, g * a = a * g)
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ A) (ht1 : t ≠ 1) (htS : t ∉ S) :
    ∃ c ∈ R, t = c * r₄ * c⁻¹ := by
  have htR : t ∈ R := hAR ht
  have ht2 : orderOf t = 2 := orderOf_eq_prime (hel.2 t ht) ht1
  obtain ⟨u, huA, hu1, hut⟩ := w183finL34_exists_ne_one_ne hcard ht ht1
  have huR : u ∈ R := hAR huA
  have hutc : u * t = t * u := by
    letI : IsMulCommutative A := hel.1
    simpa using congrArg Subtype.val (mul_comm' (⟨u, huA⟩ : A) (⟨t, ht⟩ : A))
  rcases CFSG.GH74.GLS.IVK.l34_inv_cases htR ht2 with
      ⟨c, hc, hce, -⟩ | ⟨c, hc, hce, -⟩ | ⟨c, hc, hce, -⟩ | ⟨c, hc, hce, -⟩
  · exact absurd (by rw [hce]; exact conj_mem_S hc r₁_mem_S) htS
  · exfalso
    have hcuR : c⁻¹ * u * c ∈ R :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) huR) hc
    have hxr : (c⁻¹ * u * c) * r₂ = r₂ * (c⁻¹ * u * c) := by
      rw [hce] at hutc
      calc (c⁻¹ * u * c) * r₂ = c⁻¹ * (u * (c * r₂ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * r₂ * c⁻¹) * u) * c := by rw [hutc]
        _ = r₂ * (c⁻¹ * u * c) := by group
    have hxC : ∀ y ∈ C₂, (c⁻¹ * u * c) * y = y * (c⁻¹ * u * c) := by
      intro y hy
      have hy' : y ∈ Subgroup.centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ S := hy
      obtain ⟨hyc, hyS⟩ := Subgroup.mem_inf.1 hy'
      have hyr : y * r₂ = r₂ * y := Subgroup.mem_centralizer_singleton_iff.1 hyc
      have hcyS : c * y * c⁻¹ ∈ S := conj_mem_S hc hyS
      have hcyT : (c * y * c⁻¹) * t = t * (c * y * c⁻¹) := by
        rw [hce]
        calc (c * y * c⁻¹) * (c * r₂ * c⁻¹) = c * (y * r₂) * c⁻¹ := by group
          _ = c * (r₂ * y) * c⁻¹ := by rw [hyr]
          _ = (c * r₂ * c⁻¹) * (c * y * c⁻¹) := by group
      have hcomm := hTI1 t ht ht1 (c * y * c⁻¹) hcyS hcyT u huA
      calc (c⁻¹ * u * c) * y = c⁻¹ * (u * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * u) * c := by rw [← hcomm]
        _ = y * (c⁻¹ * u * c) := by group
    rcases (CFSG.GH74.GLS.IVK.l34_cent_table.1 (c⁻¹ * u * c) hcuR hxr hxC) with h1 | h1
    · exact hu1 (by
        have := congrArg (fun z => c * z * c⁻¹) h1
        group at this
        exact this)
    · have h2 : u = c * r₂ * c⁻¹ := by
        rw [← h1]
        group
      exact hut (h2.trans hce.symm)
  · exfalso
    have hcuR : c⁻¹ * u * c ∈ R :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) huR) hc
    have hxr : (c⁻¹ * u * c) * r₃ = r₃ * (c⁻¹ * u * c) := by
      rw [hce] at hutc
      calc (c⁻¹ * u * c) * r₃ = c⁻¹ * (u * (c * r₃ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * r₃ * c⁻¹) * u) * c := by rw [hutc]
        _ = r₃ * (c⁻¹ * u * c) := by group
    have hxC : ∀ y ∈ C₃, (c⁻¹ * u * c) * y = y * (c⁻¹ * u * c) := by
      intro y hy
      have hy' : y ∈ Subgroup.centralizer ({r₃} : Set (Equiv.Perm (Fin 42))) ⊓ S := hy
      obtain ⟨hyc, hyS⟩ := Subgroup.mem_inf.1 hy'
      have hyr : y * r₃ = r₃ * y := Subgroup.mem_centralizer_singleton_iff.1 hyc
      have hcyS : c * y * c⁻¹ ∈ S := conj_mem_S hc hyS
      have hcyT : (c * y * c⁻¹) * t = t * (c * y * c⁻¹) := by
        rw [hce]
        calc (c * y * c⁻¹) * (c * r₃ * c⁻¹) = c * (y * r₃) * c⁻¹ := by group
          _ = c * (r₃ * y) * c⁻¹ := by rw [hyr]
          _ = (c * r₃ * c⁻¹) * (c * y * c⁻¹) := by group
      have hcomm := hTI1 t ht ht1 (c * y * c⁻¹) hcyS hcyT u huA
      calc (c⁻¹ * u * c) * y = c⁻¹ * (u * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * u) * c := by rw [← hcomm]
        _ = y * (c⁻¹ * u * c) := by group
    rcases (CFSG.GH74.GLS.IVK.l34_cent_table.2 (c⁻¹ * u * c) hcuR hxr hxC) with h1 | h1
    · exact hu1 (by
        have := congrArg (fun z => c * z * c⁻¹) h1
        group at this
        exact this)
    · have h2 : u = c * r₃ * c⁻¹ := by
        rw [← h1]
        group
      exact hut (h2.trans hce.symm)
  · exact ⟨c, hc, hce⟩

theorem le_S_of_ti1
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAR : A ≤ R) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ S, g * t = t * g → ∀ a ∈ A, g * a = a * g) : A ≤ S := by
  intro x hxA
  by_contra hxS
  have hx1 : x ≠ 1 := fun h => hxS (h ▸ S.one_mem)
  obtain ⟨y, hyA, hy1, hyx⟩ := w183finL34_exists_ne_one_ne hcard hxA hx1
  have key : ∀ u ∈ A, u ≠ 1 → u ∉ S → u ≠ x → False := by
    intro u huA hu1 huS hux
    have huR : u ∈ R := hAR huA
    obtain ⟨c, hc, hxc⟩ := outer_class_r4 hAR hcard hel hTI1 hxA hx1 hxS
    obtain ⟨d, hd, hud⟩ := outer_class_r4 hAR hcard hel hTI1 huA hu1 huS
    have hu_sq : u * u = 1 := by
      have := hel.2 u huA
      rwa [pow_two] at this
    have hwA : x * u ∈ A := A.mul_mem hxA huA
    have hux_comm : u * x = x * u := by
      letI : IsMulCommutative A := hel.1
      simpa using congrArg Subtype.val (mul_comm' (⟨u, huA⟩ : A) (⟨x, hxA⟩ : A))
    have hw1 : x * u ≠ 1 := by
      intro h
      apply hux
      calc u = u * (x * u) := by rw [h, mul_one]
        _ = (u * x) * u := by group
        _ = (x * u) * u := by rw [hux_comm]
        _ = x * (u * u) := by group
        _ = x := by rw [hu_sq, mul_one]
    have hr42 : r₄ * r₄ = 1 := w183finL34_r4_mul_self
    have hr4inv : r₄⁻¹ = r₄ := inv_eq_of_mul_eq_one_right hr42
    have hx_r4inv : x * r₄⁻¹ ∈ S := by
      rw [hxc]
      exact comm_r4_mem_S hc
    have hr4u : r₄ * u ∈ S := by
      have hu_r4 : u * r₄ ∈ S := by
        have hX : d * r₄ * d⁻¹ * r₄⁻¹ ∈ S := comm_r4_mem_S hd
        have heq : u * r₄ = d * r₄ * d⁻¹ * r₄⁻¹ := by
          rw [hud, hr4inv]
        rwa [heq]
      have hconj := conj_mem_S r₄_mem_R hu_r4
      have heq2 : r₄ * (u * r₄) * r₄⁻¹ = r₄ * u := by group
      rwa [heq2] at hconj
    have hwS : x * u ∈ S := by
      have : x * u = (x * r₄⁻¹) * (r₄ * u) := by group
      rw [this]
      exact S.mul_mem hx_r4inv hr4u
    have hx_card :
        Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 := by
      rw [hxc]
      exact card_centralizer_conj_r4 hc
    have hw_card :
        Nat.card ↥(Subgroup.centralizer ({x * u} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 64 := by
      refine w183finL34_card_centralizer_of_mem_S_involution hwS hw1 ?_
      have := hel.2 (x * u) hwA
      rwa [pow_two] at this
    have heq : Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S =
        Subgroup.centralizer ({x * u} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
      apply le_antisymm
      · intro g hg
        obtain ⟨hgx, hgS⟩ := Subgroup.mem_inf.1 hg
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
          (hTI1 x hxA hx1 g hgS (Subgroup.mem_centralizer_singleton_iff.1 hgx)
            (x * u) hwA), hgS⟩
      · intro g hg
        obtain ⟨hgw, hgS⟩ := Subgroup.mem_inf.1 hg
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
          (hTI1 (x * u) hwA hw1 g hgS (Subgroup.mem_centralizer_singleton_iff.1 hgw)
            x hxA), hgS⟩
    have h72 : (72 : ℕ) = 64 := by
      rw [← hx_card, heq, hw_card]
    norm_num at h72
  by_cases hyS : y ∈ S
  · have hyy : y * y = 1 := by
      have := hel.2 y hyA
      rwa [pow_two] at this
    have hyx_comm : y * x = x * y := by
      letI : IsMulCommutative A := hel.1
      simpa using congrArg Subtype.val (mul_comm' (⟨y, hyA⟩ : A) (⟨x, hxA⟩ : A))
    have huS : x * y ∉ S := by
      intro h
      apply hxS
      have : x = (x * y) * y⁻¹ := by group
      rw [this]
      exact S.mul_mem h (S.inv_mem hyS)
    have hu1 : x * y ≠ 1 := by
      intro h
      apply hyx
      calc y = y * (x * y) := by rw [h, mul_one]
        _ = (y * x) * y := by group
        _ = (x * y) * y := by rw [hyx_comm]
        _ = x * (y * y) := by group
        _ = x := by rw [hyy, mul_one]
    have hux : x * y ≠ x := by
      intro h
      apply hy1
      calc y = x⁻¹ * (x * y) := by group
        _ = x⁻¹ * x := by rw [h]
        _ = 1 := by group
    exact key (x * y) (A.mul_mem hxA hyA) hu1 huS hux
  · exact key y hyA hy1 hyS hyx

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
