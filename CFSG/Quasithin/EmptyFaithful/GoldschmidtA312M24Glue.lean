module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Rho

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

@[expose] def wordG (els : List G24) (ws : List (List ℕ)) : List G24 := ws.map (evalEltL els)

theorem wordG_tab (els : List G24) (ws : List (List ℕ))
    (hws : ∀ w ∈ ws, ∀ l ∈ w, l < els.length) :
    (wordG els ws).map (tab 24) = ws.map (wordTab 24 (els.map (tab 24))) := by
  unfold wordG
  rw [List.map_map]
  refine List.map_congr_left (fun w hw => ?_)
  simp only [Function.comp_apply]
  exact tab_evalEltL els w (hws w hw)

theorem comm_eq_of_mul_eq {G : Type*} [Group G] {x u v : G} (h : x * u = v * u * x) :
    ⁅x, u⁆ = v := by
  rw [commutatorElement_def]
  calc x * u * x⁻¹ * u⁻¹ = (v * u * x) * x⁻¹ * u⁻¹ := by rw [h]
    _ = v := by group

theorem comm_surj_of_enum {gens : List G24} {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK 24 (gens.map (tab 24)) L par) {u : G24} {tu : List ℕ} (htu : tab 24 u = tu)
    (hc : ∀ t ∈ L, ∃ s ∈ L, compTab s tu = compTab (compTab t tu) s) :
    ∀ v ∈ Subgroup.closure {x | x ∈ gens},
      ∃ x ∈ Subgroup.closure {x | x ∈ gens}, ⁅x, u⁆ = v := by
  obtain ⟨hmem, -, hreach⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective gens h
  intro v hv
  obtain ⟨s, hs, hsc⟩ := hc _ ((hmem v).mp hv)
  obtain ⟨x, hx, rfl⟩ := hreach s hs
  refine ⟨x, hx, comm_eq_of_mul_eq ?_⟩
  apply eq_of_tab_eq (n := 24)
  rw [tab_mul, tab_mul, tab_mul, htu]
  exact hsc

theorem inv_list_of_gens {α : Type} [MulAction G24 α] (gens : List G24) (L : List α)
    (h : ∀ g ∈ gens, ∀ x ∈ L, g • x ∈ L) :
    ∀ z ∈ Subgroup.closure {g | g ∈ gens}, ∀ x ∈ L, z • x ∈ L := by
  intro z hz
  induction hz using Subgroup.closure_induction_right with
  | one => intro x hx; simpa using hx
  | mul_right x hx y hy ih => intro p hp; rw [mul_smul]; exact ih _ (h y hy p hp)
  | mul_inv_cancel x hx y hy ih =>
    exact right_inv_of_right (fun z => ∀ p ∈ L, z • p ∈ L) y
      (fun x hx p hp => by rw [mul_smul]; exact hx _ (h y hy p hp)) ih

theorem perfectCore_alt {α : Type} [Fintype α] [DecidableEq α] (h5 : 5 ≤ Nat.card α) :
    perfectCore (alternatingGroup α) = alternatingGroup α :=
  perfectCore_eq_self_of_perfect (commutator_alternatingGroup_eq_self h5)

theorem eq_alt_of_card {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (H : Subgroup (Equiv.Perm α)) (hc : Nat.card H = Nat.card (alternatingGroup α)) :
    H = alternatingGroup α := by
  have h2 := two_mul_nat_card_alternatingGroup (α := α)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx : H.index ≤ 2 := by
    have h1 := H.index_mul_card
    rw [← h2, hc] at h1
    have := Nat.eq_of_mul_eq_mul_right (hc ▸ hpos) h1
    exact this.le
  exact (Subgroup.eq_of_le_of_card_ge (Equiv.Perm.alternatingGroup_le_of_index_le_two hidx)
    hc.le).symm

theorem card_range_ker_eq {Z : Subgroup G24} {H : Type} [Group H] (ρ : ↥Z →* H) {a b : ℕ}
    (hZ : Nat.card Z = a * b) (ha : a ∣ Nat.card ρ.range) (hb : b ∣ Nat.card ρ.ker)
    (ha0 : 0 < a) (hb0 : 0 < b) : Nat.card ρ.range = a ∧ Nat.card ρ.ker = b := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨k, hk⟩ := hb
  have h := card_ker_mul ρ
  rw [hZ, hr, hk] at h
  have hab : 0 < a * b := Nat.mul_pos ha0 hb0
  have hrk : r * k = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hab ?_
    calc a * b * (r * k) = a * r * (b * k) := by ring
      _ = a * b * 1 := by rw [← h]; ring
  have hr1 : r = 1 := Nat.eq_one_of_mul_eq_one_right hrk
  have hk1 : k = 1 := Nat.eq_one_of_mul_eq_one_left hrk
  exact ⟨by rw [hr, hr1, mul_one], by rw [hk, hk1, mul_one]⟩

theorem ker_eq_of_card {Z V : Subgroup G24} {H : Type} [Group H] (ρ : ↥Z →* H) (hVZ : V ≤ Z)
    (hV : V.subgroupOf Z ≤ ρ.ker) {a b : ℕ} (hZ : Nat.card Z = a * b) (hVb : Nat.card V = b)
    (ha : a ∣ Nat.card ρ.range) (ha0 : 0 < a) (hb0 : 0 < b) :
    Nat.card ρ.range = a ∧ ρ.ker = V.subgroupOf Z := by
  have hVc : Nat.card (V.subgroupOf Z) = b := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVZ).toEquiv, hVb]
  have hdvd : b ∣ Nat.card ρ.ker := hVc ▸ Subgroup.card_dvd_of_le hV
  obtain ⟨h1, h2⟩ := card_range_ker_eq ρ hZ ha hdvd ha0 hb0
  exact ⟨h1, (Subgroup.eq_of_le_of_card_ge hV (by rw [h2, hVc])).symm⟩

theorem fix_of_gens {Γ α : Type} [Group Γ] [MulAction Γ α] (gens : Set Γ) (L : List α)
    (h : ∀ g ∈ gens, ∀ x ∈ L, g • x = x) : ∀ v ∈ Subgroup.closure gens, ∀ x ∈ L, v • x = x := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro x _; exact one_smul _ x
  | mul a b _ _ ha hb => intro x hx; rw [mul_smul, hb x hx, ha x hx]
  | inv a _ ha => intro x hx; rw [inv_smul_eq_iff]; exact (ha x hx).symm

theorem listHom_eq_one_of_fix {Γ α : Type} [Group Γ] [MulAction Γ α] [DecidableEq α]
    (Z : Subgroup Γ) (L : List α) (hnd : L.Nodup) (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L)
    (z : ↥Z) (h : ∀ x ∈ L, (z : Γ) • x = x) : listHom Z L hnd hZ z = 1 := by
  ext i
  have := listHom_eq_of Z L hnd hZ z i i (h _ (List.getElem_mem i.2)).symm
  simp [this]

theorem isSolvable_of_card_two_pow {V : Type} [Group V] [Finite V] {n : ℕ}
    (h : Nat.card V = 2 ^ n) : Group.IsSolvable V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (IsPGroup.of_card h).isNilpotent
  infer_instance

theorem isExt_of_perfect_member {G : Type} [Group G] [Finite G] {T B Z : Subgroup G}
    (hB : B ∈ lFamily T) (hZ : B ⊔ T = Z) (hperf : perfectCore Z = Z) {H : Type} [Group H]
    [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (f : ↥Z →* H)
    (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hPY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (hV : PV ↥f.ker) (hQ : PY (↥Z ⧸ f.ker)) : IsExt ↥B PV PY := by
  have hZZ : ⁅Z, Z⁆ = Z := by
    have := perfectCore_perfect Z
    rwa [hperf] at this
  exact A312ExtShapes.isExt_of_perfect_simple_quotient hB hZ le_rfl hZZ.le hZZ hnab f hf hker
    hPV hPY f.ker hV hQ

end CFSG.Quasithin.A312M24
