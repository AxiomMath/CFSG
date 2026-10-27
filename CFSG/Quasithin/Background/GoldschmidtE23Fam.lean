module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace GE23

section Fam

variable {G : Type*} [Group G] [Finite G] {ι : Type*}

omit [Finite G] in
theorem indep_mono {s t : Finset ι} (hst : s ⊆ t) (A : ι → Subgroup G)
    (hind : ∀ i ∈ t, A i ⊓ ⨆ j ∈ t, ⨆ (_ : j ≠ i), A j = ⊥) :
    ∀ i ∈ s, A i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), A j = ⊥ := by
  intro i hi
  refine le_bot_iff.1 ?_
  calc A i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), A j ≤ A i ⊓ ⨆ j ∈ t, ⨆ (_ : j ≠ i), A j :=
      inf_le_inf_left _ (biSup_mono fun j hj => hst hj)
    _ = ⊥ := hind i (hst hi)

omit [Finite G] in
theorem card_iSup_of_indep [DecidableEq ι] (s : Finset ι) (A : ι → Subgroup G)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (hind : ∀ i ∈ s, A i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), A j = ⊥) :
    Nat.card ↥(⨆ i ∈ s, A i) = ∏ i ∈ s, Nat.card ↥(A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hcomm' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, x * y = y * x :=
      fun i hi j hj hij => hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hind' := indep_mono (Finset.subset_insert a s) A hind
    rw [Finset.iSup_insert, Finset.prod_insert ha, ← ih hcomm' hind']
    set W : Subgroup G := ⨆ i ∈ s, A i with hW
    have hWle : W ≤ Subgroup.centralizer (A a : Set G) := by
      refine iSup₂_le fun i hi y hy => ?_
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      exact hcomm a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi)) x hx y hy
    have hcomA : ∀ x ∈ A a, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (hWle hy) x hx
    have hinf : A a ⊓ W = ⊥ := by
      refine le_bot_iff.1 ?_
      calc A a ⊓ W ≤ A a ⊓ ⨆ j ∈ insert a s, ⨆ (_ : j ≠ a), A j := by
            refine inf_le_inf_left _ (iSup₂_le fun i hi => ?_)
            exact le_iSup₂_of_le (f := fun (j : ι) (_ : j ∈ insert a s) =>
              ⨆ (_ : j ≠ a), A j) i (Finset.mem_insert_of_mem hi)
              (le_iSup_of_le (fun h => ha (h ▸ hi)) le_rfl)
        _ = ⊥ := hind a (Finset.mem_insert_self a s)
    have := B2F.card_sup_mul_card_inf_of_commute hcomA
    rw [hinf, Subgroup.card_bot, mul_one] at this
    exact this

theorem isSylowTwoOf_iSup [DecidableEq ι] (s : Finset ι) (A B : ι → Subgroup G)
    (hsyl : ∀ i ∈ s, IsSylowTwoOf (B i) (A i))
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (hind : ∀ i ∈ s, A i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), A j = ⊥) :
    IsSylowTwoOf (⨆ i ∈ s, B i) (⨆ i ∈ s, A i) := by
  have hBA : ∀ i ∈ s, B i ≤ A i := fun i hi => (hsyl i hi).1
  have hcommB : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ B i, ∀ b ∈ B j, a * b = b * a :=
    fun i hi j hj hij a ha b hb => hcomm i hi j hj hij a (hBA i hi ha) b (hBA j hj hb)
  have hindB : ∀ i ∈ s, B i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), B j = ⊥ := by
    intro i hi
    refine le_bot_iff.1 ?_
    calc B i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), B j ≤ A i ⊓ ⨆ j ∈ s, ⨆ (_ : j ≠ i), A j :=
        inf_le_inf (hBA i hi) (iSup₂_mono fun j hj => iSup_mono fun _ => hBA j hj)
      _ = ⊥ := hind i hi
  have hcardA := card_iSup_of_indep s A hcomm hind
  have hcardB := card_iSup_of_indep s B hcommB hindB
  have hle : (⨆ i ∈ s, B i) ≤ ⨆ i ∈ s, A i := iSup₂_mono fun i hi => hBA i hi
  have hrel : ∀ i ∈ s, (B i).relIndex (A i) * Nat.card ↥(B i) = Nat.card ↥(A i) := by
    intro i hi
    have := Subgroup.relIndex_mul_card (B i) (A i)
    rwa [inf_of_le_left (hBA i hi)] at this
  have hrel0 : (⨆ i ∈ s, B i).relIndex (⨆ i ∈ s, A i) * Nat.card ↥(⨆ i ∈ s, B i) =
      Nat.card ↥(⨆ i ∈ s, A i) := by
    have := Subgroup.relIndex_mul_card (⨆ i ∈ s, B i) (⨆ i ∈ s, A i)
    rwa [inf_of_le_left hle] at this
  refine ⟨hle, ?_, ?_⟩
  ·
    have : ∀ i ∈ s, ∃ m : ℕ, Nat.card ↥(B i) = 2 ^ m := fun i hi => (hsyl i hi).2.1.exists_card_eq
    choose! m hm using this
    refine IsPGroup.of_card (n := ∑ i ∈ s, m i) ?_
    rw [hcardB, Finset.prod_congr rfl hm, Finset.prod_pow_eq_pow_sum]
  ·
    have hprod : (⨆ i ∈ s, B i).relIndex (⨆ i ∈ s, A i) = ∏ i ∈ s, (B i).relIndex (A i) := by
      have hpos : 0 < Nat.card ↥(⨆ i ∈ s, B i) := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [hrel0, hcardA, hcardB, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i hi => (hrel i hi).symm
    show ¬ 2 ∣ (⨆ i ∈ s, B i).relIndex (⨆ i ∈ s, A i)
    rw [hprod]
    intro h
    obtain ⟨i, hi, h2⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h
    exact (hsyl i hi).2.2 h2

theorem eq_of_isSylowTwoOf_le {Y P W : Subgroup G} (hP : IsSylowTwoOf P Y) (hPW : P ≤ W)
    (hWY : W ≤ Y) (hW : IsPGroup 2 W) : W = P := by
  have hs := B6.isSylowTwoOf_mono hP hPW hWY
  obtain ⟨n, hn⟩ := hW.index (P.subgroupOf W)
  have hn0 : n = 0 := by
    by_contra hne
    exact hs.2.2 (by rw [hn]; exact dvd_pow_self 2 hne)
  have h1 : P.relIndex W = 1 := by
    show (P.subgroupOf W).index = 1
    rw [hn, hn0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hPW

omit [Finite G] in
theorem exists_conj_gen [DecidableEq (Subgroup G)] (s : Finset (Subgroup G))
    (P : Subgroup G → Subgroup G)
    (hcomm : ∀ H ∈ s, ∀ H' ∈ s, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a)
    (hPH : ∀ H ∈ s, P H ≤ H)
    (hgen : ∀ H ∈ s, ∃ w ∈ H, H ≤ P H ⊔ (P H).map (MulAut.conj w).toMonoidHom) :
    ∃ g ∈ ⨆ H ∈ s, H, ∀ H ∈ s, H ≤ P H ⊔ (P H).map (MulAut.conj g).toMonoidHom := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert a s ha ih =>
    have hmem : ∀ H ∈ s, H ∈ insert a s := fun H hH => Finset.mem_insert_of_mem hH
    obtain ⟨gs, hgs, hgsP⟩ := ih (fun H hH H' hH' => hcomm H (hmem H hH) H' (hmem H' hH'))
      (fun H hH => hPH H (hmem H hH)) (fun H hH => hgen H (hmem H hH))
    obtain ⟨w, hw, hwP⟩ := hgen a (Finset.mem_insert_self a s)
    have hcg : ∀ y ∈ a, gs * y = y * gs := by
      intro y hy
      have : (⨆ H ∈ s, H) ≤ Subgroup.centralizer ({y} : Set G) := by
        refine iSup₂_le fun H hH h hh => ?_
        refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hcomm H (hmem H hH) a (Finset.mem_insert_self a s) (fun e => ha (e ▸ hH)) h hh z
          hy).symm
      exact (Subgroup.mem_centralizer_iff.1 (this hgs) y rfl).symm
    refine ⟨gs * w, ?_, ?_⟩
    · rw [Finset.iSup_insert]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgs) (Subgroup.mem_sup_left hw)
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hHs
      · have key : ∀ p ∈ P H, gs * w * p * (gs * w)⁻¹ = w * p * w⁻¹ := by
          intro p hp
          have hy : w * p * w⁻¹ ∈ H :=
            H.mul_mem (H.mul_mem hw (hPH H (Finset.mem_insert_self _ _) hp)) (H.inv_mem hw)
          have h1 := hcg _ hy
          calc gs * w * p * (gs * w)⁻¹ = gs * (w * p * w⁻¹) * gs⁻¹ := by group
            _ = w * p * w⁻¹ := by rw [h1]; group
        have : (P H).map (MulAut.conj (gs * w)).toMonoidHom =
            (P H).map (MulAut.conj w).toMonoidHom := by
          ext x
          simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, (key p hp).symm⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, key p hp⟩
        rw [this]
        exact hwP
      · have hwp : ∀ p ∈ P H, w * p * w⁻¹ = p := by
          intro p hp
          have := hcomm a (Finset.mem_insert_self a s) H (hmem H hHs) (fun e => ha (e ▸ hHs)) w hw p
            (hPH H (hmem H hHs) hp)
          rw [this]; group
        have key : ∀ p ∈ P H, gs * w * p * (gs * w)⁻¹ = gs * p * gs⁻¹ := by
          intro p hp
          calc gs * w * p * (gs * w)⁻¹ = gs * (w * p * w⁻¹) * gs⁻¹ := by group
            _ = gs * p * gs⁻¹ := by rw [hwp p hp]
        have : (P H).map (MulAut.conj (gs * w)).toMonoidHom =
            (P H).map (MulAut.conj gs).toMonoidHom := by
          ext x
          simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, (key p hp).symm⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, key p hp⟩
        rw [this]
        exact hgsP H hHs

end Fam

end GE23

end CFSG.Quasithin
