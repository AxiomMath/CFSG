module

public import CFSG.Sporadic.Schreier.RuCheckSylow
public import CFSG.Sporadic.Schreier.RuLocalSub

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem rep_of_eqA {n : ℕ} {a b : Array ℕ} {g : Equiv.Perm (Fin n)} (hb : Rep n b g)
    (h : eqA n a b = true) : Rep n a g := by
  intro x
  have := (allLt_iff.1 h) x x.2
  rw [beq_iff_eq] at this
  rw [this, hb x]

theorem conj_mem_of_closure {G : Type*} [Group G] {H : Subgroup G} [Finite H] {Y : Set G}
    (hH : H = Subgroup.closure Y) {s : G} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ H) :
    s ∈ Subgroup.normalizer (H : Set G) := by
  have hmap : H.map (MulAut.conj s).toMonoidHom ≤ H := by
    rw [hH, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [← hH]
    exact hs y hy
  have hcard : Nat.card (H.map (MulAut.conj s).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have heq : H.map (MulAut.conj s).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hmap hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hmap ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', he⟩ := hh
    have : h' = h := by
      have := he
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact (MulAut.conj s).injective (by simpa [MulAut.conj_apply] using this)
    rw [← this]
    exact hh'

theorem le_normalizer_of_gens {G : Type*} [Group G] {H S : Subgroup G} [Finite H] {X Y : Set G}
    (hH : H = Subgroup.closure Y) (hS : S = Subgroup.closure X)
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ H) : S ≤ Subgroup.normalizer (H : Set G) := by
  rw [hS, Subgroup.closure_le]
  intro x hx
  exact conj_mem_of_closure hH (h x hx)

theorem ruSGens_getD_mem (i : ℕ) : ruSGens.getD i 1 ∈ ruS := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ruSGens[i]? with
  | none => exact ruS.one_mem
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem ruRGens_getD_mem (i : ℕ) : ruRGens.getD i 1 ∈ ruR := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ruRGens[i]? with
  | none => exact ruR.one_mem
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

@[expose] def ruSGenS (i : ℕ) : ruS := ⟨ruSGens.getD i 1, ruSGens_getD_mem i⟩

theorem rep_ruSF
    {j : ℕ} (hj : j < 4) : Rep 1920 (ruSF j) (ruResFPerm (ruSGens.getD j 1)) :=
  rep_of_eqA (rep_ruResF (rep_ruSGens j hj) (ruS_leC (ruSGens_getD_mem j)))
    (ruGens_check.2.2.2.2.2.2.2.2.2.2.1 j hj)

theorem rep_ruRF
    {i : ℕ} (hi : i < 5) : Rep 1920 (ruRF i) (ruResFPerm (ruRGens.getD i 1)) :=
  rep_of_eqA (rep_ruResF (rep_ruRGens i hi) (ruR_leC (ruRGens_getD_mem i)))
    (ruGens_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi)

theorem ruResFPerm_mul
    {x y : Equiv.Perm (Fin 4060)} (hx : x ∈ ruC) (hy : y ∈ ruC) :
    ruResFPerm (x * y) = ruResFPerm x * ruResFPerm y := by
  rw [ruResFPerm_of_mem (ruC.mul_mem hx hy), ruResFPerm_of_mem hx, ruResFPerm_of_mem hy, ← map_mul]
  rfl

theorem ruResFPerm_inv
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruC) :
    ruResFPerm x⁻¹ = (ruResFPerm x)⁻¹ := by
  rw [ruResFPerm_of_mem (ruC.inv_mem hx), ruResFPerm_of_mem hx, ← map_inv]
  rfl

theorem mem_ruR_of_sift
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC)
    (ht : Rep 1920 t (ruResFPerm g)) (h : ruSift 1920 (ruField1920 4) ruRBase t = true) :
    g ∈ ruR :=
  mem_of_sift1920 ruChainR_sub hg ((ruChain_sift ruChainR_check.1 ht).1 h)

theorem ruSGens_memC'
    (i : ℕ) : ruSGens.getD i 1 ∈ ruC := ruS_leC (ruSGens_getD_mem i)

theorem ruRGens_memC'
    (i : ℕ) : ruRGens.getD i 1 ∈ ruC := ruR_leC (ruRGens_getD_mem i)

theorem ruS_conj_R
    {i j : ℕ} (hi : i < 5) (hj : j < 4) :
    ruSGens.getD j 1 * ruRGens.getD i 1 * (ruSGens.getD j 1)⁻¹ ∈ ruR := by
  have hs := ruSGens_memC' j
  have hr := ruRGens_memC' i
  apply mem_ruR_of_sift (ruC.mul_mem (ruC.mul_mem hs hr) (ruC.inv_mem hs)) _
    (ruSylow_check.2.1 i hi j hj)
  rw [ruResFPerm_mul (ruC.mul_mem hs hr) (ruC.inv_mem hs), ruResFPerm_mul hs hr,
    ruResFPerm_inv hs]
  exact rep_compA (rep_compA (rep_ruSF hj) (rep_ruRF hi))
    (rep_inv_of_isInvA (rep_ruSF hj) (ruSylow_check.1 j hj))

theorem ruS_comm_R
    {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    ruSGens.getD i 1 * ruSGens.getD j 1 * (ruSGens.getD i 1)⁻¹ * (ruSGens.getD j 1)⁻¹ ∈ ruR := by
  have hs := ruSGens_memC' i
  have ht := ruSGens_memC' j
  apply mem_ruR_of_sift (ruC.mul_mem (ruC.mul_mem (ruC.mul_mem hs ht) (ruC.inv_mem hs))
    (ruC.inv_mem ht)) _ (ruSylow_check.2.2.1 i hi j hj)
  rw [ruResFPerm_mul (ruC.mul_mem (ruC.mul_mem hs ht) (ruC.inv_mem hs)) (ruC.inv_mem ht),
    ruResFPerm_mul (ruC.mul_mem hs ht) (ruC.inv_mem hs), ruResFPerm_mul hs ht, ruResFPerm_inv hs,
    ruResFPerm_inv ht]
  exact rep_compA (rep_compA (rep_compA (rep_ruSF hi) (rep_ruSF hj))
    (rep_inv_of_isInvA (rep_ruSF hi) (ruSylow_check.1 i hi)))
    (rep_inv_of_isInvA (rep_ruSF hj) (ruSylow_check.1 j hj))

theorem ruS_sq_R
    {i : ℕ} (hi : i < 4) : ruSGens.getD i 1 * ruSGens.getD i 1 ∈ ruR := by
  have hs := ruSGens_memC' i
  apply mem_ruR_of_sift (ruC.mul_mem hs hs) _ (ruSylow_check.2.2.2.1 i hi)
  rw [ruResFPerm_mul hs hs]
  exact rep_compA (rep_ruSF hi) (rep_ruSF hi)

theorem ruS1_memR :
    ruSGens.getD 1 1 ∈ ruR :=
  mem_ruR_of_sift (ruSGens_memC' 1) (rep_ruSF (by norm_num)) ruSylow_check.2.2.2.2.1

instance :
    Finite ruR := Nat.finite_of_card_ne_zero (by rw [card_ruR]; norm_num)

instance :
    Finite ruS := Nat.finite_of_card_ne_zero (by rw [card_ruS]; norm_num)

theorem mem_ruSGens_iff {g : Equiv.Perm (Fin 4060)} :
    g ∈ ruSGens ↔ ∃ j < 4, ruSGens.getD j 1 = g := by
  constructor
  · intro hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    exact ⟨j, by rw [ruSGens_length] at hj; exact hj, List.getD_eq_getElem _ _ hj⟩
  · rintro ⟨j, hj, rfl⟩
    rw [List.getD_eq_getElem _ _ (by rw [ruSGens_length]; exact hj)]
    exact List.getElem_mem _

theorem mem_ruRGens_iff {g : Equiv.Perm (Fin 4060)} :
    g ∈ ruRGens ↔ ∃ i < 5, ruRGens.getD i 1 = g := by
  constructor
  · intro hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    exact ⟨i, by rw [ruRGens_length] at hi; exact hi, List.getD_eq_getElem _ _ hi⟩
  · rintro ⟨i, hi, rfl⟩
    rw [List.getD_eq_getElem _ _ (by rw [ruRGens_length]; exact hi)]
    exact List.getElem_mem _

theorem ruS_le_normalizer_R :
    ruS ≤ Subgroup.normalizer (ruR : Set (Equiv.Perm (Fin 4060))) := by
  apply le_normalizer_of_gens (X := {g | g ∈ ruSGens}) (Y := {g | g ∈ ruRGens}) rfl rfl
  intro x hx y hy
  obtain ⟨j, hj, rfl⟩ := mem_ruSGens_iff.1 hx
  obtain ⟨i, hi, rfl⟩ := mem_ruRGens_iff.1 hy
  exact ruS_conj_R hi hj

abbrev ruRS : Subgroup ruS := ruR.subgroupOf ruS

instance ruRS_normal :
    ruRS.Normal :=
  (Subgroup.normal_subgroupOf_iff ruR_leS).2 fun h k hh hk => by
    have := ruS_le_normalizer_R hk
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this h).1 hh

end CFSG.Sporadic.RuSchreier
