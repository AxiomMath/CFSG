module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDatum
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDParabolicLE3
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
public import CFSG.Permutation.SupportedAdjacent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.StandardType.TypeBDatum
open Multiplicative

namespace TypeDDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma tbD_permAut_conj_sgnAut {m p : ℕ} (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    (permAut (p := p) τ * sgnAut (p := p) j * (permAut (p := p) τ)⁻¹ :
      MulAut (Fin m → Multiplicative (ZMod p))) = sgnAut (p := p) (τ j) := by
  have hu : ∀ f i, toAdd (permAut (p := p) τ f (τ i)) = (1 : ZMod p) * toAdd (f i) := by
    intro f i
    rw [permAut_apply]; simp
  have h := IsSignedPerm.mul_sgnAut (p := p) (u := permAut (p := p) τ) (π := τ)
    (ε := fun _ => 1) hu j
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem tbD_map_conj_evenSignedSupportedAut {m p : ℕ} [Fact p.Prime]
    (S : Finset (Fin m)) (τ : Equiv.Perm (Fin m)) :
    (evenSignedSupportedAut m p S).map (MulAut.conj (permAut (p := p) τ)).toMonoidHom =
      evenSignedSupportedAut m p (S.image τ) := by
  classical
  unfold evenSignedSupportedAut
  rw [MonoidHom.map_closure]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨a, ha, b, hb, hab, rfl⟩, rfl⟩
      refine ⟨τ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, τ b,
        Finset.mem_image.mpr ⟨b, hb, rfl⟩, fun h => hab (τ.injective h), ?_⟩
      change permAut (p := p) τ * permAut (p := p) (Equiv.swap a b) *
        (permAut (p := p) τ)⁻¹ = permAut (p := p) (Equiv.swap (τ a) (τ b))
      rw [permAut_conj_swap]
    · rintro ⟨a, ha, b, hb, hab, rfl⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      refine ⟨permAut (p := p) (Equiv.swap a' b'), ?_, ?_⟩
      · exact ⟨a', ha', b', hb', fun h => hab (by rw [h]), rfl⟩
      · change permAut (p := p) τ * permAut (p := p) (Equiv.swap a' b') *
          (permAut (p := p) τ)⁻¹ = permAut (p := p) (Equiv.swap (τ a') (τ b'))
        rw [permAut_conj_swap]
  · ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨a, ha, b, hb, hab, rfl⟩, rfl⟩
      refine ⟨τ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, τ b,
        Finset.mem_image.mpr ⟨b, hb, rfl⟩, fun h => hab (τ.injective h), ?_⟩
      rw [map_mul]
      change (permAut (p := p) τ * sgnAut (p := p) a * (permAut (p := p) τ)⁻¹) *
          (permAut (p := p) τ * sgnAut (p := p) b * (permAut (p := p) τ)⁻¹) =
            sgnAut (p := p) (τ a) * sgnAut (p := p) (τ b)
      rw [tbD_permAut_conj_sgnAut, tbD_permAut_conj_sgnAut]
    · rintro ⟨a, ha, b, hb, hab, rfl⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      refine ⟨sgnAut (p := p) a' * sgnAut (p := p) b', ?_, ?_⟩
      · exact ⟨a', ha', b', hb', fun h => hab (by rw [h]), rfl⟩
      · rw [map_mul]
        change (permAut (p := p) τ * sgnAut (p := p) a' * (permAut (p := p) τ)⁻¹) *
            (permAut (p := p) τ * sgnAut (p := p) b' * (permAut (p := p) τ)⁻¹) =
              sgnAut (p := p) (τ a') * sgnAut (p := p) (τ b')
        rw [tbD_permAut_conj_sgnAut, tbD_permAut_conj_sgnAut]

private theorem tbD_map_conj_evenSignedAut {m p : ℕ} [Fact p.Prime] (τ : Equiv.Perm (Fin m)) :
    (evenSignedAut m p).map (MulAut.conj (permAut (p := p) τ)).toMonoidHom =
      evenSignedAut m p := by
  unfold evenSignedAut
  rw [tbD_map_conj_evenSignedSupportedAut Finset.univ τ, Finset.image_univ_equiv]

private lemma tbD_liftBs_prodCongr {G : Type} [Group G] {Bs : Subgroup G}
    {W W₀ : Type} [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) (P : MulAut W) (σ : MulAut W) :
    liftBs ((MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ) σ = liftBs Θ (P * σ * P⁻¹) := by
  set Θ' := (MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ with hΘ'
  refine MulEquiv.ext fun b => ?_
  obtain ⟨⟨w, u⟩, rfl⟩ := Θ'.surjective b
  rw [liftBs_apply Θ' σ w u]
  rw [show Θ' (w, u) = Θ (P w, u) from rfl]
  rw [liftBs_apply Θ (P * σ * P⁻¹) (P w) u]
  change Θ (P (σ w), u) = Θ ((P * σ * P⁻¹) (P w), u)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

private def tbD_permAutHom (p m : ℕ) :
    Equiv.Perm (Fin m) →* MulAut (Fin m → Multiplicative (ZMod p)) where
  toFun := permAut (p := p)
  map_one' := by
    refine MulEquiv.ext fun f => funext fun i => ?_
    change permAut (p := p) 1 f i = (1 : MulAut (Fin m → Multiplicative (ZMod p))) f i
    simp [permAut_apply]
  map_mul' σ τ := by
    refine MulEquiv.ext fun f => funext fun i => ?_
    change permAut (p := p) (σ * τ) f i =
      (permAut (p := p) σ * permAut (p := p) τ) f i
    simp only [MulAut.mul_apply, permAut_apply, Function.comp_apply]
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

@[simp] private theorem tbD_permAutHom_apply (p m : ℕ) (σ : Equiv.Perm (Fin m)) :
    tbD_permAutHom p m σ = permAut (p := p) σ := rfl

private def tbD_tlEquivSucc (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    Fin ((k - 1) + 1) ≃ ↥(Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) where
  toFun a := ⟨⟨m - k + a.val, by omega⟩, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.le_add_right (m - k) a.val⟩
  invFun j := ⟨j.1.val - (m - k), by
    have hj : m - k ≤ j.1.val := by
      have h := j.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    omega⟩
  left_inv a := by
    apply Fin.ext
    dsimp only
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp only
    have hj : m - k ≤ j.1.val := by
      have h := j.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    omega

private theorem tbD_permAut_fixingSubgroup_le {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hm2 : 2 ≤ m)
    {Q : Subgroup (MulAut (Fin m → Multiplicative (ZMod p)))}
    (hQ : ∀ j : {j : Fin m // m - k ≤ j.val},
      typeDSimple m p hm2 j.1 ∈ Q) :
    (fixingSubgroup (Equiv.Perm (Fin m)) ((Finset.univ.filter (fun i : Fin m => m - k ≤ i.val) : Set (Fin m))ᶜ)).map
      (tbD_permAutHom p m) ≤ Q := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  let eTl : Fin ((k - 1) + 1) ≃ ↥Tl := tbD_tlEquivSucc m k hk hkm
  have hfix := CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_closure_adjacent
    Tl eTl
  rw [hfix, MonoidHom.map_closure, Subgroup.closure_le]
  rintro x ⟨y, ⟨j, rfl⟩, rfl⟩
  rw [tbD_permAutHom_apply]
  set a' : Fin m := (eTl j.castSucc : Fin m) with ha'def
  set b' : Fin m := (eTl j.succ : Fin m) with hb'def
  have ha'val : a'.val = m - k + j.val := by
    rw [ha'def]
    rfl
  have hb'val : b'.val = m - k + j.val + 1 := by
    rw [hb'def]
    rfl
  have hlt : a'.val + 1 < m := by rw [ha'val]; omega
  let j' : {j : Fin m // m - k ≤ j.val} := ⟨a', by rw [ha'val]; omega⟩
  have hQj := hQ j'
  have hif : typeDSimple m p hm2 j'.1 =
      permAut (p := p) (Equiv.swap j'.1 ⟨j'.1.val + 1, hlt⟩) := by
    unfold typeDSimple
    rw [dif_pos hlt]
  rw [hif] at hQj
  have hb'eq : (⟨a'.val + 1, hlt⟩ : Fin m) = b' := by
    apply Fin.ext
    simp only [ha'val, hb'val]
  rw [hb'eq] at hQj
  exact hQj

private theorem tbD_permAut_swap_mem {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hm2 : 2 ≤ m)
    {Q : Subgroup (MulAut (Fin m → Multiplicative (ZMod p)))}
    (hQ : ∀ j : {j : Fin m // m - k ≤ j.val},
      typeDSimple m p hm2 j.1 ∈ Q)
    {a b : Fin m} (ha : m - k ≤ a.val) (hb : m - k ≤ b.val) (hab : a ≠ b) :
    permAut (p := p) (Equiv.swap a b) ∈ Q := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  have haTl : a ∈ Tl := by
    simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
  have hbTl : b ∈ Tl := by
    simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb
  have hmem : Equiv.swap a b ∈ fixingSubgroup (Equiv.Perm (Fin m)) ((Tl : Set (Fin m))ᶜ) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hya : y ≠ a := fun h => hy (h ▸ haTl)
    have hyb : y ≠ b := fun h => hy (h ▸ hbTl)
    simp only [Equiv.Perm.smul_def]
    exact Equiv.swap_apply_of_ne_of_ne hya hyb
  exact tbD_permAut_fixingSubgroup_le hk hkm hm2 hQ (Subgroup.mem_map_of_mem (tbD_permAutHom p m) hmem)

private theorem tbD_closure_last_le_evenSignedSupported {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hm2 : 2 ≤ m) (hk3 : 3 ≤ k) :
    Subgroup.closure (Set.range fun j :
        {j : Fin m // m - k ≤ j.val} => typeDSimple m p hm2 j) ≤
      evenSignedSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  rw [Subgroup.closure_le]
  rintro σ ⟨j, rfl⟩
  have hjTl : j.1 ∈ Tl := by
    simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.2
  by_cases hlt : j.1.val + 1 < m
  · simp only [typeDSimple]
    rw [dif_pos hlt]
    have hsuccTl : (⟨j.1.val + 1, hlt⟩ : Fin m) ∈ Tl := by
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
      have hj : m - k ≤ j.1.val := j.2
      omega
    exact Subgroup.subset_closure (Or.inl ⟨j.1, hjTl, ⟨j.1.val + 1, hlt⟩, hsuccTl, by
      intro h
      have hh : j.1.val = (⟨j.1.val + 1, hlt⟩ : Fin m).val := congrArg Fin.val h
      rw [show (⟨j.1.val + 1, hlt⟩ : Fin m).val = j.1.val + 1 from rfl] at hh
      omega, rfl⟩)
  · simp only [typeDSimple]
    rw [dif_neg hlt]
    have hk2 : 2 ≤ k := by omega
    have hm2Tl : (⟨m - 2, by omega⟩ : Fin m) ∈ Tl := by
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hm1Tl : (⟨m - 1, by omega⟩ : Fin m) ∈ Tl := by
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hperm : permAut (p := p) (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)) ∈ evenSignedSupportedAut m p Tl :=
      Subgroup.subset_closure (Or.inl ⟨⟨m - 2, by omega⟩, hm2Tl, ⟨m - 1, by omega⟩, hm1Tl, by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_mk] at hh
        omega, rfl⟩)
    have hsgn : sgnAut (p := p) (⟨m - 2, by omega⟩ : Fin m) * sgnAut (p := p) (⟨m - 1, by omega⟩ : Fin m) ∈ evenSignedSupportedAut m p Tl :=
      Subgroup.subset_closure (Or.inr ⟨⟨m - 2, by omega⟩, hm2Tl, ⟨m - 1, by omega⟩, hm1Tl, by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_mk] at hh
        omega, rfl⟩)
    exact Subgroup.mul_mem _ hperm hsgn

private theorem tbD_dinv_mem_of_hcan {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hm2 : 2 ≤ m)
    {Q : Subgroup (MulAut (Fin m → Multiplicative (ZMod p)))}
    (hQ : ∀ j : {j : Fin m // m - k ≤ j.val}, typeDSimple m p hm2 j.1 ∈ Q)
    {x2 x1 : Fin m} (hx2 : m - k ≤ x2.val) (hx1 : m - k ≤ x1.val) (hx21 : x2 ≠ x1)
    (hcan : sgnAut (p := p) x2 * sgnAut (p := p) x1 ∈ Q)
    {a b : Fin m} (ha : m - k ≤ a.val) (hb : m - k ≤ b.val) (hab : a ≠ b) :
    sgnAut (p := p) a * sgnAut (p := p) b ∈ Q := by
  have hE : ∀ c : Fin m, m - k ≤ c.val → c ≠ x1 →
      sgnAut (p := p) c * sgnAut (p := p) x1 ∈ Q := by
    intro c hc hc1
    by_cases hc2 : c = x2
    · rw [hc2]
      exact hcan
    · have hsw : permAut (p := p) (Equiv.swap x2 c) ∈ Q :=
        tbD_permAut_swap_mem hk hkm hm2 hQ hx2 hc (Ne.symm hc2)
      have h1 : permAut (p := p) (Equiv.swap x2 c) *
          (sgnAut (p := p) x2 * sgnAut (p := p) x1) * (permAut (p := p) (Equiv.swap x2 c))⁻¹ =
          sgnAut (p := p) c * sgnAut (p := p) x1 := by
        have e := fun j : Fin m => tbD_permAut_conj_sgnAut (p := p) (Equiv.swap x2 c) j
        calc permAut (p := p) (Equiv.swap x2 c) * (sgnAut (p := p) x2 * sgnAut (p := p) x1) *
              (permAut (p := p) (Equiv.swap x2 c))⁻¹ =
            (permAut (p := p) (Equiv.swap x2 c) * sgnAut (p := p) x2 *
              (permAut (p := p) (Equiv.swap x2 c))⁻¹) *
            (permAut (p := p) (Equiv.swap x2 c) * sgnAut (p := p) x1 *
              (permAut (p := p) (Equiv.swap x2 c))⁻¹) := by group
          _ = sgnAut (p := p) c * sgnAut (p := p) x1 := by
            rw [e x2, e x1, Equiv.swap_apply_left,
              Equiv.swap_apply_of_ne_of_ne (Ne.symm hx21) (Ne.symm hc1)]
      rw [← h1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsw hcan) (Subgroup.inv_mem _ hsw)
  by_cases hb1 : b = x1
  · rw [hb1]
    exact hE a ha (fun h => hab (h.trans hb1.symm))
  · have hbE := hE b hb hb1
    by_cases ha1 : a = x1
    · rw [ha1, sgnAut_mul_comm]
      exact hbE
    · have haE := hE a ha ha1
      have hsq : sgnAut (p := p) x1 * sgnAut (p := p) x1 = 1 := OrthExcEven.sgnAut_mul_self x1
      have hbE' : sgnAut (p := p) x1 * sgnAut (p := p) b ∈ Q := by
        rw [sgnAut_mul_comm]
        exact hbE
      have hprod : sgnAut (p := p) a * sgnAut (p := p) b =
          (sgnAut (p := p) a * sgnAut (p := p) x1) * (sgnAut (p := p) x1 * sgnAut (p := p) b) := by
        calc sgnAut (p := p) a * sgnAut (p := p) b =
            sgnAut (p := p) a * (sgnAut (p := p) x1 * sgnAut (p := p) x1) *
              sgnAut (p := p) b := by rw [hsq, mul_one]
          _ = _ := by simp only [mul_assoc]
      rw [hprod]
      exact Subgroup.mul_mem _ haE hbE'

private theorem tbD_evenSignedSupported_last_le_closure {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hm2 : 2 ≤ m) (hk3 : 3 ≤ k) :
    evenSignedSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) ≤
      Subgroup.closure (Set.range fun j :
          {j : Fin m // m - k ≤ j.val} => typeDSimple m p hm2 j) := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  let Q : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
    Subgroup.closure (Set.range fun j : {j : Fin m // m - k ≤ j.val} =>
      typeDSimple m p hm2 j)
  have hQ : ∀ j : {j : Fin m // m - k ≤ j.val},
      typeDSimple m p hm2 j.1 ∈ Q := by
    intro j
    exact Subgroup.subset_closure ⟨j, rfl⟩
  rw [evenSignedSupportedAut, Subgroup.closure_le]
  rintro σ (hσ | hσ)
  · rcases hσ with ⟨a, haTl, b, hbTl, hab, rfl⟩
    have haTl' : m - k ≤ a.val := by
      have h := haTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hbTl' : m - k ≤ b.val := by
      have h := hbTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    exact tbD_permAut_swap_mem hk hkm hm2 hQ haTl' hbTl' hab
  · rcases hσ with ⟨a, haTl, b, hbTl, hab, rfl⟩
    have haTl' : m - k ≤ a.val := by
      have h := haTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hbTl' : m - k ≤ b.val := by
      have h := hbTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hm2Tl : (⟨m - 2, by omega⟩ : Fin m) ∈ Tl := by
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hm1Tl : (⟨m - 1, by omega⟩ : Fin m) ∈ Tl := by
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hcan : sgnAut (p := p) (⟨m - 2, by omega⟩ : Fin m) * sgnAut (p := p) (⟨m - 1, by omega⟩ : Fin m) ∈ Q := by
      have hds : typeDSimple m p hm2 (⟨m - 2, by omega⟩ : Fin m) =
          permAut (p := p) (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)) := by
        unfold typeDSimple
        rw [dif_pos (by simp only [Fin.val_mk]; omega : (⟨m - 2, by omega⟩ : Fin m).val + 1 < m)]
        congr 2
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      have hds2 : typeDSimple m p hm2 (⟨m - 1, by omega⟩ : Fin m) =
          permAut (p := p) (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)) *
            (sgnAut (p := p) (⟨m - 2, by omega⟩ : Fin m) * sgnAut (p := p) (⟨m - 1, by omega⟩ : Fin m)) := by
        unfold typeDSimple
        rw [dif_neg (by simp only [Fin.val_mk]; omega : ¬ (⟨m - 1, by omega⟩ : Fin m).val + 1 < m)]
      have hsq : permAut (p := p) (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)) *
          permAut (p := p) (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)) = 1 := by
        have h := permAut_swap_sq (p := p) (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)
        simpa [sq] using h
      have hprod : typeDSimple m p hm2 (⟨m - 2, by omega⟩ : Fin m) *
          typeDSimple m p hm2 (⟨m - 1, by omega⟩ : Fin m) =
          sgnAut (p := p) (⟨m - 2, by omega⟩ : Fin m) * sgnAut (p := p) (⟨m - 1, by omega⟩ : Fin m) := by
        rw [hds, hds2, ← mul_assoc, hsq, one_mul]
      rw [← hprod]
      exact Subgroup.mul_mem _
        (hQ ⟨⟨m - 2, by omega⟩, by simpa only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] using hm2Tl⟩)
        (hQ ⟨⟨m - 1, by omega⟩, by simpa only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] using hm1Tl⟩)
    exact tbD_dinv_mem_of_hcan hk hkm hm2 hQ (x2 := ⟨m - 2, by omega⟩) (x1 := ⟨m - 1, by omega⟩)
      (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
      (by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_mk] at hh; omega)
      hcan haTl' hbTl' hab

private theorem tbD_evenSignedSupported_eq_closure_last {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hm2 : 2 ≤ m) (hk3 : 3 ≤ k) :
    evenSignedSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) =
      Subgroup.closure (Set.range fun j :
          {j : Fin m // m - k ≤ j.val} => typeDSimple m p hm2 j) :=
  le_antisymm (tbD_evenSignedSupported_last_le_closure hk hkm hm2 hk3)
    (tbD_closure_last_le_evenSignedSupported hk hkm hm2 hk3)

theorem ggTBJTypeD_sideDatum_evenSupported {G : Type} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (evenSignedAut m p).map (liftBs Θ))
    {S : Finset (Fin m)} (hS : 3 ≤ S.card) (hc : 1 ≤ m - S.card) (hc3 : m - S.card ≤ 3)
    (hJ : ggAutomizer J Bs = (evenSignedSupportedAut m p S).map (liftBs Θ)) :
    (m - S.card = 1 → GGResSideDatum p Bs X J) ∧
      (2 ≤ m - S.card → GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  have hm2 : 2 ≤ m := by omega
  have hkm : S.card ≤ m := by omega
  let Tl : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => m - S.card ≤ i.val)
  have hTlcard : Tl.card = S.card := by
    have h : (S.card - 1) + 1 = Tl.card := by
      have h0 := Fintype.card_congr (tbD_tlEquivSucc m S.card (by omega) hkm)
      rw [Fintype.card_fin] at h0
      rw [h0]
      exact Fintype.card_coe Tl
    omega
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin m), Tl.image τ = S := by
    let f1 : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
    let f2 : Fin S.card ↪ Fin m := (Tl.orderEmbOfFin hTlcard).toEmbedding
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding f2 f1
    have hτi : ∀ i, τ (f2 i) = f1 i := by
      intro i
      have hh := congrArg (fun e : Fin S.card ↪ Fin m => e i) hτ
      simpa only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] using hh
    refine ⟨τ, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hy' : y ∈ Set.range (Tl.orderEmbOfFin hTlcard) := by
        rw [Finset.range_orderEmbOfFin]
        exact hy
      obtain ⟨i, rfl⟩ := hy'
      have := hτi i
      change τ ((Tl.orderEmbOfFin hTlcard) i) = (S.orderEmbOfFin rfl) i at this
      rw [this]
      exact Finset.orderEmbOfFin_mem S rfl i
    · intro hx
      have hx' : x ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨i, rfl⟩ := hx'
      refine Finset.mem_image.mpr ⟨(Tl.orderEmbOfFin hTlcard) i,
        Finset.orderEmbOfFin_mem Tl hTlcard i, ?_⟩
      exact hτi i
  let P : MulAut (Fin m → Multiplicative (ZMod p)) := permAut (p := p) τ
  let Θ' : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs :=
    (MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ
  have hliftΘ' : liftBs Θ' = (liftBs Θ).comp (MulAut.conj P).toMonoidHom :=
    MonoidHom.ext fun σ => tbD_liftBs_prodCongr Θ P σ
  have hX' : ggAutomizer X Bs = (evenSignedAut m p).map (liftBs Θ') := by
    rw [hliftΘ', ← Subgroup.map_map, tbD_map_conj_evenSignedAut, hX]
  have hJ' : ggAutomizer J Bs = (evenSignedSupportedAut m p Tl).map (liftBs Θ') := by
    rw [hliftΘ', ← Subgroup.map_map, tbD_map_conj_evenSignedSupportedAut, hτ, hJ]
  obtain ⟨V, hV, hVmod, ι, φ, h, α, hlin, hrefl, hpair, ⟨f, hf⟩, hclos, hφ⟩ :=
    exists_typeD_datum_of_evenSignedAut hp2 hm hBs Θ' hX'
  letI : AddCommGroup V := hV
  letI : Module (ZMod p) V := hVmod
  have hJcl : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Fin m // m - S.card ≤ j.val} => φ j.1) := by
    rw [hJ', tbD_evenSignedSupported_eq_closure_last (by omega) hkm hm2 hS,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, hφ j.1⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, (hφ j.1).symm⟩
  exact ggTBJTypeDParabolicLE3_endD (n := m) (c := m - S.card) hp2 hc hc3 (by omega) rfl rfl
    hlin hrefl hpair hf hclos hJcl

theorem exists_signed_on_castSucc_of_mem_evenSignedSupportedAut
    {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (π : Fin (r + 1) ≃ Fin n) (S : Finset (Fin r))
    {α : MulAut (Fin n → Multiplicative (ZMod p))}
    (hα : α ∈ evenSignedSupportedAut n p
      (S.image (fun i : Fin r => π i.castSucc))) :
    ∃ (σ : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∏ i, ε i = 1) ∧
      (∀ (v : Fin n → Multiplicative (ZMod p)) (i : Fin r),
        Multiplicative.toAdd (α v (π (σ i).castSucc)) =
          ε i * Multiplicative.toAdd (v (π i.castSucc))) ∧
      (∀ v : Fin n → Multiplicative (ZMod p),
        α v (π (Fin.last r)) = v (π (Fin.last r))) := by
  classical
  have hαwhole : α ∈ evenSignedAut n p := by
    rw [evenSignedAut]
    unfold evenSignedSupportedAut
    refine (Subgroup.closure_mono ?_) hα
    rintro x (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact Or.inl ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩
    · exact Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩
  have hαG : α ∈ DScalarTorus.evenSignedGroup (p := p) (N := n) := by
    rw [← tbD_evenSignedAut_eq_evenSignedGroup hp2]
    exact hαwhole
  obtain ⟨σ₀, c, hc, hcp, hact⟩ := hαG
  let last : Fin n := π (Fin.last r)
  have hlast_not : last ∉ S.image (fun i : Fin r => π i.castSucc) := by
    intro hmem
    obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hmem
    exact (Fin.castSucc_lt_last i).ne (π.injective hpi)
  let f : Fin n → Multiplicative (ZMod p) :=
    Pi.mulSingle last (Multiplicative.ofAdd (1 : ZMod p))
  have hf : ∀ i ∈ S.image (fun i : Fin r => π i.castSucc), f i = 1 := by
    intro i hi
    change Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) last
      (Multiplicative.ofAdd (1 : ZMod p)) i = 1
    refine Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p))
      ?_ (Multiplicative.ofAdd (1 : ZMod p))
    intro hil
    obtain ⟨a, ha, hpi⟩ := Finset.mem_image.mp hi
    exact (Fin.castSucc_lt_last a).ne (π.injective (by rw [hpi, hil]))
  have hfixf : α f = f :=
    CFSG.StandardType.FrameBs.evenSignedSupportedAut_fix hf α hα
  have hf_last : Multiplicative.toAdd (f last) = 1 := by
    simp [f]
  have hlast_fix : σ₀ last = last := by
    by_contra hne
    let j₀ : Fin n := σ₀.symm last
    have hj₀ : j₀ ≠ last := by
      intro h
      apply hne
      have h' := congrArg σ₀ h
      rw [Equiv.apply_symm_apply] at h'
      exact h'.symm
    have hf_j₀ : Multiplicative.toAdd (f j₀) = 0 := by
      have hfj : f j₀ = 1 := by
        change Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) last
          (Multiplicative.ofAdd (1 : ZMod p)) j₀ = 1
        exact Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p))
          hj₀ (Multiplicative.ofAdd (1 : ZMod p))
      rw [hfj]
      rfl
    have h := hact f j₀
    rw [show σ₀ j₀ = last from Equiv.apply_symm_apply σ₀ last, hfixf] at h
    have h1 : (1 : ZMod p) = 0 := by simpa [hf_last, hf_j₀] using h
    exact one_ne_zero h1
  have hclast : c last = 1 := by
    have h := hact f last
    rw [hlast_fix, hfixf, hf_last, mul_one] at h
    exact h.symm
  let e : Fin r ≃ {j : Fin n // j ≠ last} :=
    (finSuccAboveEquiv (Fin.last r)).trans
      (π.subtypeEquiv (p := fun j : Fin (r + 1) => j ≠ Fin.last r)
        (q := fun j : Fin n => j ≠ last) (by
          intro j
          constructor
          · intro hj h
            exact hj (π.injective h)
          · intro hj h
            exact hj (congrArg π h)))
  have hσ₀_iff : ∀ x : Fin n, (σ₀ x ≠ last) ↔ (x ≠ last) := by
    intro x
    constructor
    · intro hx hxl
      apply hx
      rw [hxl, hlast_fix]
    · intro hx hcon
      apply hx
      exact σ₀.injective (by rw [hcon, hlast_fix])
  let τ : Equiv.Perm {j : Fin n // j ≠ last} := σ₀.subtypePerm hσ₀_iff
  let σ : Equiv.Perm (Fin r) := e.trans (τ.trans e.symm)
  have hσe : ∀ i : Fin r, e (σ i) = τ (e i) := by
    intro i
    change e (e.symm (τ (e i))) = τ (e i)
    rw [Equiv.apply_symm_apply]
  have hπσ : ∀ i : Fin r, π (σ i).castSucc = σ₀ (π i.castSucc) := by
    intro i
    have hval := congrArg Subtype.val (hσe i)
    simpa only [e, τ, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
      finSuccAboveEquiv_apply, Fin.succAbove_last_apply, Equiv.Perm.subtypePerm_apply]
      using hval
  let ε : Fin r → ZMod p := fun i => c (π i.castSucc)
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => hc (π i.castSucc)
  have hprod_pi : (∏ j : Fin n, c j) = ∏ i : Fin (r + 1), c (π i) := by
    simpa using (Equiv.prod_comp π (fun j => c j)).symm
  have hprod_active : (∏ i : Fin r, ε i) = 1 := by
    have h := hprod_pi
    rw [Fin.prod_univ_castSucc] at h
    rw [hcp, hclast, mul_one] at h
    exact h.symm
  refine ⟨σ, ε, hε, hprod_active, ?_, ?_⟩
  · intro v i
    rw [hπσ i]
    exact hact v (π i.castSucc)
  · intro v
    apply Multiplicative.toAdd.injective
    simpa only [hlast_fix, hclast, one_mul] using hact v last

end TypeDDatum

end CFSG.StandardType

end
