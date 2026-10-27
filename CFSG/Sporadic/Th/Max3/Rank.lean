module

public import CFSG.Sporadic.Th.Max3.Involutions
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate10508
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtraspecialAb

public section

namespace CFSG.Sporadic.Th.Max3.Rank

open CFSG.Sporadic.Th.Native CFSG.Certificates

theorem eq_one_or_eq_z
    {w : J} (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨b, hb⟩ := (ExtraspecialNF.mem_zpowers_iff_exists symplectic_rel).1 hw
  rcases ExtraspecialNF.zmod_two_cases b with rfl | rfl
  · left
    rw [← hb, ZMod.val_zero, pow_zero]
  · right
    rw [← hb, ExtraspecialNF.val_one_two, pow_one]

private theorem mul_comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  have := hE.1
  exact setLike_mul_comm ha hb

theorem card_le_of_le_Q
    {E : Subgroup J} (hEQ : E ≤ Q) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : Nat.card E ≤ 32 := by
  refine CFSG.Quasithin.D4Hex.card_abelian_le_32 (z := z) card_Q (fun a ha b hb => ?_)
    (fun w hw hc => ?_) hEQ hE
  · have h := AltQuot.comm_mem_zpowers ha hb
    rw [commutatorElement_def] at h
    exact eq_one_or_eq_z h
  · have hcen : (⟨w, hw⟩ : Q) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2)
    rw [center_Q] at hcen
    exact eq_one_or_eq_z hcen

private theorem card_le_of_x_mem_count {G : Type*} [Group G] {M Q E : Subgroup G} {x : G}
    (κ : ↥M →* Equiv.Perm (Fin 9)) (hκQ : ∀ g : ↥M, κ g = 1 ↔ (g : G) ∈ Q)
    (hxM : x ∈ M) (hκx : κ ⟨x, hxM⟩ = aPerm)
    (hconj : ∀ m ∈ M, m ∉ Q → m * m = 1 → ∃ g ∈ M, g * m * g⁻¹ = x)
    (ν : Fin 512 → G) (hν : ∀ g ∈ Q, ∃ k, ν k = g)
    (C : List (Fin 512)) (hC16 : C.length = 16) (hmemC : ∀ k, ν k * x = x * ν k → k ∈ C)
    (hcommC : ∀ k ∈ C, ∀ l ∈ C, ν k * ν l = ν l * ν k)
    (ℓ : Fin 12 → G) (hℓM : ∀ i, ℓ i ∈ M) (hℓκ : ∀ i, κ ⟨ℓ i, hℓM i⟩ = rkPerm i)
    (hℓx : ∀ i, ℓ i * x = x * ℓ i)
    (D : Fin 12 → List (Fin 512)) (hmemD : ∀ i, ∀ k ∈ C, ν k * ℓ i = ℓ i * ν k → k ∈ D i)
    (hD8 : ∀ i, (D i).length ≤ 8)
    (hTA : ∀ i, rkTypeB i = false → ∀ k ∈ C, (ν k * ℓ i) ^ 2 ≠ 1)
    (hTB : ∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
      rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
      rkPerm j ≠ rkPerm i * aPerm → ((D i).filter fun k => decide (k ∈ D j)).length ≤ 4)
    (hC1 : ∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
      ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j)
    (hEM : E ≤ M) (hE : CFSG.Open.IsElemAbelian 2 E) (hxE : x ∈ E) : Nat.card E ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isElemAbelian hE ha hb
  have hE2 : ∀ a ∈ E, a * a = 1 := fun a ha => by
    rw [← sq]
    exact hE.2 a ha
  have hEcomm : ∀ a b : ↥E, a * b = b * a := fun a b => by
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hEab _ a.2 _ b.2
  let ψ : ↥E →* Equiv.Perm (Fin 9) := κ.comp (Subgroup.inclusion hEM)
  have hψ : ∀ e : ↥E, ψ e = κ ⟨e, hEM e.2⟩ := fun e => rfl
  have hψ1 : ∀ e : ↥E, ψ e = 1 ↔ (e : G) ∈ Q := fun e => by
    rw [hψ]
    exact hκQ _
  have hψx : ψ ⟨x, hxE⟩ = aPerm := by
    rw [hψ]
    exact hκx
  have hψ2 : ∀ e : ↥E, ψ e * ψ e = 1 := fun e => by
    have hee : e * e = 1 := by
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one]
      exact hE2 _ e.2
    rw [← map_mul, hee, map_one]
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hsupp : ∀ e : ↥E, (e : G) ∉ Q → (Finset.univ.filter fun j => ψ e j ≠ j).card = 8 := by
    intro e heQ
    obtain ⟨g, hgM, hg⟩ := hconj _ (hEM e.2) heQ (hE2 _ e.2)
    have e1 : (⟨g, hgM⟩ : ↥M) * ⟨(e : G), hEM e.2⟩ * (⟨g, hgM⟩ : ↥M)⁻¹ = ⟨x, hxM⟩ := by
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hg
    have hk : κ ⟨g, hgM⟩ * ψ e * (κ ⟨g, hgM⟩)⁻¹ = aPerm := by
      rw [hψ, ← map_inv κ, ← map_mul κ, ← map_mul κ, e1, hκx]
    have h : (κ ⟨g, hgM⟩ * ψ e * (κ ⟨g, hgM⟩)⁻¹).support.card = (ψ e).support.card :=
      Equiv.Perm.card_support_conj
    rw [hk, show aPerm.support.card = 8 by decide] at h
    exact h.symm
  have hxQ : ∀ e : ↥E, ((e * ⟨x, hxE⟩ : ↥E) : G) ∈ Q ↔ (e : G) * x ∈ Q := fun e => by
    rw [Subgroup.coe_mul]
  have hkey : ∀ e : ↥E, (e : G) ∉ Q → (e : G) * x ∉ Q → ∃ i, ψ e = rkPerm i := by
    intro e heQ hexQ
    have hσ2 : ∀ j, ψ e (ψ e j) = j := fun j => by
      rw [← Equiv.Perm.mul_apply, hψ2, Equiv.Perm.one_apply]
    have hσa : ψ e * aPerm = aPerm * ψ e := by
      rw [← hψx, ← map_mul, ← map_mul, hEcomm]
    have hcomm : ∀ j, ψ e (aPerm j) = aPerm (ψ e j) := fun j => by
      rw [← Equiv.Perm.mul_apply, hσa, Equiv.Perm.mul_apply]
    have hexQ' : ((e * ⟨x, hxE⟩ : ↥E) : G) ∉ Q := fun h => hexQ ((hxQ e).1 h)
    have hσne : ∃ j, ψ e j ≠ aPerm j := by
      by_contra h
      push Not at h
      have h1 : ψ (e * ⟨x, hxE⟩) = 1 := by
        rw [map_mul, hψx, Equiv.ext h]
        decide
      exact hexQ' ((hψ1 _).1 h1)
    have hc2 := hsupp (e * ⟨x, hxE⟩) hexQ'
    rw [map_mul, hψx] at hc2
    simp only [Equiv.Perm.mul_apply] at hc2
    have hfix : ∀ k : Fin 9, aPerm k = k → k = 8 := by decide
    have h8 : ψ e 8 = 8 :=
      hfix _ ((hcomm 8).symm.trans (congrArg (ψ e) (by decide : aPerm 8 = 8)))
    have htup : ⇑(ψ e) = rkTup (ψ e 0) (ψ e 2) (ψ e 4) (ψ e 6) := by
      funext j
      fin_cases j
      · rfl
      · exact (congrArg (ψ e) (by decide : (1 : Fin 9) = aPerm 0)).trans (hcomm 0)
      · rfl
      · exact (congrArg (ψ e) (by decide : (3 : Fin 9) = aPerm 2)).trans (hcomm 2)
      · rfl
      · exact (congrArg (ψ e) (by decide : (5 : Fin 9) = aPerm 4)).trans (hcomm 4)
      · rfl
      · exact (congrArg (ψ e) (by decide : (7 : Fin 9) = aPerm 6)).trans (hcomm 6)
      · exact h8
    have hcand : RkCand (rkTup (ψ e 0) (ψ e 2) (ψ e 4) (ψ e 6)) := by
      rw [← htup]
      exact ⟨hσ2, hσne, hsupp e heQ, hc2⟩
    obtain ⟨i, hi⟩ := hC1 _ _ _ _ hcand
    exact ⟨i, Equiv.ext fun j => (congrFun htup j).trans (hi j)⟩
  have hsub : ∀ σ ∈ ψ.range, σ = 1 ∨ σ = aPerm ∨ ∃ i, σ = rkPerm i := by
    intro σ hσ
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.1 hσ
    by_cases heQ : (e : G) ∈ Q
    · exact Or.inl ((hψ1 e).2 heQ)
    by_cases hexQ : (e : G) * x ∈ Q
    · have h1 : ψ (e * ⟨x, hxE⟩) = 1 := (hψ1 _).2 ((hxQ e).2 hexQ)
      rw [map_mul, hψx] at h1
      exact Or.inr (Or.inl ((mul_eq_one_iff_eq_inv.1 h1).trans (by decide)))
    · exact Or.inr (Or.inr (hkey e heQ hexQ))
  have hfib : ∀ (e : ↥E) (i : Fin 12), ψ e = rkPerm i → ∃ k ∈ C, ν k * ℓ i = (e : G) := by
    intro e i hei
    have hk : κ ⟨(e : G), hEM e.2⟩ = κ ⟨ℓ i, hℓM i⟩ :=
      (hψ e).symm.trans (hei.trans (hℓκ i).symm)
    have hnQ : (e : G) * (ℓ i)⁻¹ ∈ Q := by
      have h : κ (⟨(e : G), hEM e.2⟩ * (⟨ℓ i, hℓM i⟩ : ↥M)⁻¹) = 1 := by
        rw [map_mul, map_inv, hk, mul_inv_cancel]
      have h2 := (hκQ _).1 h
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      exact h2
    obtain ⟨k, hk'⟩ := hν _ hnQ
    refine ⟨k, hmemC k ?_, ?_⟩
    · rw [hk']
      exact ((show Commute (e : G) x from hEab _ e.2 _ hxE).mul_left
        (show Commute (ℓ i) x from hℓx i).inv_left).eq
    · rw [hk', inv_mul_cancel_right]
  have hfibD : ∀ (e : ↥E) (i : Fin 12), ψ e = rkPerm i → ∀ k : Fin 512, ν k ∈ E → k ∈ D i := by
    intro e i hei k' hk'E
    obtain ⟨k, hkC, hke⟩ := hfib e i hei
    have hk'C : k' ∈ C := hmemC k' (hEab _ hk'E _ hxE)
    refine hmemD i k' hk'C ?_
    have hℓ : ℓ i = (ν k)⁻¹ * e := by
      rw [← hke, inv_mul_cancel_left]
    rw [hℓ]
    exact ((show Commute (ν k') (ν k) from hcommC k' hk'C k hkC).inv_right.mul_right
      (show Commute (ν k') (e : G) from hEab _ hk'E _ e.2)).eq
  have htype : ∀ (e : ↥E) (i : Fin 12), ψ e = rkPerm i → rkTypeB i = true := by
    intro e i hei
    by_contra hB
    obtain ⟨k, hkC, hke⟩ := hfib e i hei
    have hne := hTA i (by simpa using hB) k hkC
    rw [hke] at hne
    exact hne (hE.2 _ e.2)
  have hcount : ∀ l : List (Fin 512), (∀ e : ↥E, ψ e = 1 → ∃ k ∈ l, ν k = (e : G)) →
      Nat.card ψ.ker ≤ l.length := by
    intro l hl
    have hl' : ∀ e : ↥ψ.ker, ∃ k : ↥l.toFinset, ν k.1 = ((e : ↥E) : G) := fun e => by
      obtain ⟨k, hk, he⟩ := hl e.1 (MonoidHom.mem_ker.1 e.2)
      exact ⟨⟨k, List.mem_toFinset.2 hk⟩, he⟩
    choose f hf using hl'
    have hf' : Function.Injective f := fun a b hab => by
      have h : ((a : ↥E) : G) = ((b : ↥E) : G) := by rw [← hf a, ← hf b, hab]
      exact Subtype.ext (Subtype.ext h)
    calc Nat.card ψ.ker ≤ Nat.card ↥l.toFinset := Nat.card_le_card_of_injective f hf'
      _ = l.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ l.length := List.toFinset_card_le l
  have hkerQ : ∀ e : ↥E, ψ e = 1 → ∃ k : Fin 512, ν k = (e : G) ∧ ν k ∈ E := fun e he => by
    obtain ⟨k, hk⟩ := hν _ ((hψ1 e).1 he)
    exact ⟨k, hk, hk ▸ e.2⟩
  have hout : ∀ S : Finset (Equiv.Perm (Fin 9)), S.card < Nat.card ψ.range →
      ∃ e : ↥E, ψ e ∉ S := by
    intro S hS
    by_contra h
    push Not at h
    have hsubS : ((ψ.range : Subgroup (Equiv.Perm (Fin 9))) : Set (Equiv.Perm (Fin 9))) ⊆ S := by
      intro σ hσ
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.1 hσ
      exact h e
    have h' := Set.ncard_le_ncard hsubS (Finset.finite_toSet S)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h'
    exact absurd hS (not_lt.2 h')
  have h14 : Nat.card ψ.range ≤ 14 := by
    by_contra hlt
    push Not at hlt
    have hS14 : (insert 1 (insert aPerm (Finset.univ.image rkPerm)) :
        Finset (Equiv.Perm (Fin 9))).card ≤ 14 := by
      have h1 := Finset.card_insert_le (1 : Equiv.Perm (Fin 9))
        (insert aPerm (Finset.univ.image rkPerm))
      have h2 := Finset.card_insert_le aPerm (Finset.univ.image rkPerm)
      have h3 : (Finset.univ.image rkPerm).card ≤ 12 :=
        Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
      omega
    obtain ⟨e, he⟩ := hout _ (lt_of_le_of_lt hS14 hlt)
    apply he
    rcases hsub (ψ e) (MonoidHom.mem_range.2 ⟨e, rfl⟩) with h | h | ⟨i, h⟩
    · rw [h]
      exact Finset.mem_insert_self _ _
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hp : IsPGroup 2 ψ.range := by
    intro σ
    obtain ⟨e, he⟩ := MonoidHom.mem_range.1 σ.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← he, sq, hψ2, Subgroup.coe_one]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpair : ({1, aPerm} : Finset (Equiv.Perm (Fin 9))).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
  have hone : 2 < Nat.card ψ.range → ∃ e : ↥E, ∃ i, ψ e = rkPerm i := by
    intro h2
    obtain ⟨e, he⟩ := hout {1, aPerm} (lt_of_le_of_lt hpair h2)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rcases hsub (ψ e) (MonoidHom.mem_range.2 ⟨e, rfl⟩) with h | h | h
    · exact absurd h he.1
    · exact absurd h he.2
    · exact ⟨e, h⟩
  have hker16 : Nat.card ψ.ker ≤ 16 := by
    have hk := hcount C fun e he => by
      obtain ⟨k, hk, hkE⟩ := hkerQ e he
      exact ⟨k, hmemC k (hEab _ hkE _ hxE), hk⟩
    rw [hC16] at hk
    exact hk
  rw [← hcard, hn]
  interval_cases n
  ·
    omega
  ·
    omega
  ·
    obtain ⟨e, i, hi⟩ := hone (by rw [hn]; norm_num)
    have hk := hcount _ fun e' he' => by
      obtain ⟨k, hk, hkE⟩ := hkerQ e' he'
      exact ⟨k, hfibD e i hi k hkE, hk⟩
    have := hk.trans (hD8 i)
    omega
  ·
    obtain ⟨e2, i, hi⟩ := hone (by rw [hn]; norm_num)
    have hquad : ({1, aPerm, rkPerm i, rkPerm i * aPerm} :
        Finset (Equiv.Perm (Fin 9))).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_))
      exact (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
    obtain ⟨e3, he3⟩ := hout _ (lt_of_le_of_lt hquad (by rw [hn]; norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he3
    obtain ⟨j, hj⟩ : ∃ j, ψ e3 = rkPerm j := by
      rcases hsub (ψ e3) (MonoidHom.mem_range.2 ⟨e3, rfl⟩) with h | h | h
      · exact absurd h he3.1
      · exact absurd h he3.2.1
      · exact h
    have hij : rkPerm i * rkPerm j = rkPerm j * rkPerm i := by
      rw [← hi, ← hj, ← map_mul, ← map_mul, hEcomm]
    have h4 := hTB i j (htype e2 i hi) (htype e3 j hj) hij (by rw [← hj]; exact he3.2.2.1)
      (by rw [← hj]; exact he3.2.2.2)
    have hk := hcount _ fun e' he' => by
      obtain ⟨k, hk, hkE⟩ := hkerQ e' he'
      exact ⟨k, List.mem_filter.2 ⟨hfibD e2 i hi k hkE, decide_eq_true (hfibD e3 j hj k hkE)⟩,
        hk⟩
    have := hk.trans h4
    omega

private theorem rkData_eq : rkData () =
    ⟨cqxList (), Array.ofFn rkRows, (Array.ofFn rkRows).map (commList (cqxList ()))⟩ :=
  rkData.eq_1 ()

private theorem rkData_C : (rkData ()).C = cqxList () := by
  rw [rkData_eq]

private theorem getElem!_ofFn {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[i.val]! = f i := by
  simp

private theorem getElem!_map_ofFn {α β : Type} [Inhabited β] {n : ℕ} (f : Fin n → α)
    (g : α → β) (i : Fin n) : ((Array.ofFn f).map g)[i.val]! = g (f i) := by
  simp

private theorem rkData_R (i : Fin 12) : (rkData ()).R[i.val]! = rkRows i := by
  rw [rkData_eq]
  exact getElem!_ofFn rkRows i

private theorem rkData_D (i : Fin 12) :
    (rkData ()).D[i.val]! = commList (cqxList ()) (rkRows i) := by
  rw [rkData_eq]
  exact getElem!_map_ofFn rkRows (commList (cqxList ())) i

private theorem kapP_eq_one_iff
    (g : ↥M) :
    ((alternatingGroup (Fin 9)).subtype.comp InvRep.kap) g = 1 ↔ (g : J) ∈ Q := by
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, OneMemClass.coe_eq_one]
  exact InvRep.kap_eq_one_iff

private theorem kapP_x :
    ((alternatingGroup (Fin 9)).subtype.comp InvRep.kap) ⟨x, x_mem_M⟩ = aPerm := by
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact InvRep.kap_genM .x

private theorem ell_mem_M (i : Fin 12) :
    nfAt (rkK0 i) * wordProd (rkWord i) ∈ M :=
  M.mul_mem (Q_le_M (AltQuot.nfAt_mem_Q _)) (wordProd_mem_M _)

private theorem kapP_ell
    (i : Fin 12) :
    ((alternatingGroup (Fin 9)).subtype.comp InvRep.kap)
      ⟨nfAt (rkK0 i) * wordProd (rkWord i), ell_mem_M i⟩ = rkPerm i := by
  have e : (⟨nfAt (rkK0 i) * wordProd (rkWord i), ell_mem_M i⟩ : ↥M) =
      ⟨nfAt (rkK0 i), Q_le_M (AltQuot.nfAt_mem_Q (rkK0 i))⟩ * InvRep.wordM (rkWord i) :=
    Subtype.ext (by rw [Subgroup.coe_mul, InvRep.wordM])
  have h1 : InvRep.kap (⟨nfAt (rkK0 i), Q_le_M (AltQuot.nfAt_mem_Q (rkK0 i))⟩ : ↥M) = 1 :=
    InvRep.kap_eq_one_iff.2 (AltQuot.nfAt_mem_Q (rkK0 i))
  rw [rkPerm, MonoidHom.comp_apply, Subgroup.coe_subtype, e, map_mul, h1, one_mul,
    InvRep.kap_wordM]

private theorem isRows_ell
    (i : Fin 12) : IsRows (rkRows i) (nfAt (rkK0 i) * wordProd (rkWord i)) :=
  (isRows_nfAt _).mul (IsRows.word isRows_x isRows_y _)

private theorem mem_cqxList
    (k : Fin 512) (hk : nfAt k * x = x * nfAt k) : k ∈ cqxList () := by
  refine List.mem_filter.2 ⟨List.mem_finRange k, ?_⟩
  rw [((isRows_nfAt k).mul isRows_x).rows_eq (by rw [hk]; exact isRows_x.mul (isRows_nfAt k))]
  exact eqRows_iff.2 rfl

private theorem mem_commList
    (i : Fin 12) (k : Fin 512) (hk : k ∈ cqxList ())
    (hkg : nfAt k * (nfAt (rkK0 i) * wordProd (rkWord i)) =
      nfAt (rkK0 i) * wordProd (rkWord i) * nfAt k) :
    k ∈ commList (cqxList ()) (rkRows i) := by
  refine List.mem_filter.2 ⟨hk, ?_⟩
  rw [((isRows_nfAt k).mul (isRows_ell i)).rows_eq
    (by rw [hkg]; exact (isRows_ell i).mul (isRows_nfAt k))]
  exact eqRows_iff.2 rfl

private theorem card_le_of_x_mem
    {E : Subgroup J} (hEM : E ≤ M)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hxE : x ∈ E) : Nat.card E ≤ 32 := by
  obtain ⟨hC1, hF⟩ := (Certificates.certificate10508)
  have hF' : RkFacts (rkData ()) := hF
  unfold RkFacts at hF'
  obtain ⟨hC16, hCcomm, hRx, hD8, hTA, hTB⟩ := hF'
  rw [rkData_C] at hC16 hCcomm hTA
  simp only [rkData_R] at hRx hTA
  simp only [rkData_D] at hD8 hTB
  have hcommC : ∀ k ∈ cqxList (), ∀ l ∈ cqxList (), nfAt k * nfAt l = nfAt l * nfAt k :=
    fun k hk l hl => ((isRows_nfAt k).mul (isRows_nfAt l)).eq_of_eqRows
      ((isRows_nfAt l).mul (isRows_nfAt k)) (hCcomm k hk l hl)
  have hℓx : ∀ i, nfAt (rkK0 i) * wordProd (rkWord i) * x =
      x * (nfAt (rkK0 i) * wordProd (rkWord i)) := fun i =>
    ((isRows_ell i).mul isRows_x).eq_of_eqRows (isRows_x.mul (isRows_ell i)) (hRx i)
  have hTA' : ∀ i, rkTypeB i = false → ∀ k ∈ cqxList (),
      (nfAt k * (nfAt (rkK0 i) * wordProd (rkWord i))) ^ 2 ≠ 1 := fun i hB k hk =>
    (((isRows_nfAt k).mul (isRows_ell i)).pow 2).ne_of_eqRows IsRows.one (hTA i hB k hk)
  exact card_le_of_x_mem_count ((alternatingGroup (Fin 9)).subtype.comp InvRep.kap)
    kapP_eq_one_iff x_mem_M kapP_x
    (fun m hm hQ hsq => InvRep.exists_conj_x_of_not_mem_Q hm hQ hsq) nfAt
    (fun g hg => InvRep.exists_nfAt_eq hg) (cqxList ()) hC16 mem_cqxList hcommC
    (fun i => nfAt (rkK0 i) * wordProd (rkWord i)) ell_mem_M kapP_ell hℓx
    (fun i => commList (cqxList ()) (rkRows i)) mem_commList hD8 hTA' hTB hC1 hEM hE hxE

theorem card_le_of_le_M
    {E : Subgroup J} (hEM : E ≤ M)
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 32 := by
  by_cases hEQ : E ≤ Q
  · exact card_le_of_le_Q hEQ fun a ha b hb => mul_comm_of_isElemAbelian hE ha hb
  obtain ⟨e, heE, heQ⟩ := SetLike.not_le_iff_exists.1 hEQ
  obtain ⟨g, hgM, hg⟩ := InvRep.exists_conj_x_of_not_mem_Q (hEM heE) heQ (by
    rw [← sq]
    exact hE.2 e heE)
  have hF : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← hF]
  refine card_le_of_x_mem ?_ (hE.map _) ⟨e, heE, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem hgM (hEM hh)) (M.inv_mem hgM)
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hg

def genB1 : Fin 4 → Fin 8 → ZMod 2 :=
  ![![1, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 1, 1, 0],
    ![1, 1, 0, 0, 0, 0, 0, 1]]

def genB2 : Fin 4 → Fin 8 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0], ![1, 0, 0, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 1, 0, 0, 1]]

def lc (B : Fin 4 → Fin 8 → ZMod 2) (u : Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun k => ∑ j, u j * B j k

private theorem genB1_bil :
    ∀ u v : Fin 4 → ZMod 2, ExtraspecialNF.bil c (lc genB1 u) (lc genB1 v) = 0 := by
  decide +kernel

private theorem genB2_bil :
    ∀ u v : Fin 4 → ZMod 2, ExtraspecialNF.bil c (lc genB2 u) (lc genB2 v) = 0 := by
  decide +kernel

private theorem genB1_qf : ∀ u : Fin 4 → ZMod 2, ExtraspecialNF.qf c (lc genB1 u) = 0 := by
  decide +kernel

private theorem genB2_qf : ∀ u : Fin 4 → ZMod 2, ExtraspecialNF.qf c (lc genB2 u) = 0 := by
  decide +kernel

private theorem genB1_inj : ∀ u v : Fin 4 → ZMod 2, lc genB1 u = lc genB1 v → u = v := by
  decide +kernel

private theorem genB2_inj : ∀ u v : Fin 4 → ZMod 2, lc genB2 u = lc genB2 v → u = v := by
  decide +kernel

private theorem genB_span :
    ∀ i : Fin 8, ∃ u v : Fin 4 → ZMod 2, Pi.single i 1 = lc genB1 u + lc genB2 v := by
  decide +kernel

private theorem isElemAbelian_closure {G : Type*} [Group G] {S : Set G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hS2 : ∀ a ∈ S, a ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun a ha b hb _ => hS a ha b hb
  refine ⟨hcomm, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem a ha => exact hS2 a ha
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    rw [(show Commute a b from setLike_mul_comm ha hb).mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

private theorem exists_elemAbelian
    (B : Fin 4 → Fin 8 → ZMod 2)
    (hbil : ∀ u v : Fin 4 → ZMod 2, ExtraspecialNF.bil c (lc B u) (lc B v) = 0)
    (hqf : ∀ u : Fin 4 → ZMod 2, ExtraspecialNF.qf c (lc B u) = 0)
    (hinj : ∀ u v : Fin 4 → ZMod 2, lc B u = lc B v → u = v) :
    ∃ A : Subgroup J, A ≤ Q ∧ CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 5 ∧
      ∀ s u, ExtraspecialNF.nf z q s (lc B u) ∈ A := by
  have hsymm : ∀ i j, c i j = c j i := fun i j => c_symm j i
  have hdiag : ∀ i, c i i = 0 := by decide
  let S : Set J := Set.range fun p : ZMod 2 × (Fin 4 → ZMod 2) =>
    ExtraspecialNF.nf z q p.1 (lc B p.2)
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
    dsimp only
    rw [ExtraspecialNF.nf_mul_comm symplectic_rel hsymm hdiag, hbil, ZMod.val_zero, pow_zero,
      mul_one]
  have hS2 : ∀ a ∈ S, a ^ 2 = 1 := by
    rintro _ ⟨p, rfl⟩
    dsimp only
    rw [ExtraspecialNF.nf_sq symplectic_rel hsymm, hqf, ZMod.val_zero, pow_zero]
  have hEA : CFSG.Open.IsElemAbelian 2 (Subgroup.closure S) := isElemAbelian_closure hS hS2
  have hSQ : Subgroup.closure S ≤ Q := by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact nf_mem_Q _ _
  refine ⟨Subgroup.closure S, hSQ, hEA, le_antisymm ?_ ?_,
    fun s u => Subgroup.subset_closure ⟨(s, u), rfl⟩⟩
  · exact (card_le_of_le_Q hSQ fun a ha b hb => mul_comm_of_isElemAbelian hEA ha hb).trans
      (by norm_num)
  · have hf : Function.Injective fun p : ZMod 2 × (Fin 4 → ZMod 2) =>
        (⟨ExtraspecialNF.nf z q p.1 (lc B p.2), Subgroup.subset_closure ⟨p, rfl⟩⟩ :
          ↥(Subgroup.closure S)) := by
      intro p p' h
      have h0 := congrArg Subtype.val h
      dsimp only at h0
      have h' := nf_injective_generic (a₁ := (p.1, lc B p.2)) (a₂ := (p'.1, lc B p'.2))
        (by rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair]; exact h0)
      obtain ⟨hs, hv⟩ := Prod.mk.inj h'
      exact Prod.ext hs (hinj _ _ hv)
    have h32 : Nat.card (ZMod 2 × (Fin 4 → ZMod 2)) = 2 ^ 5 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, ZMod.card,
        Fintype.card_fin]
      norm_num
    rw [← h32]
    exact Nat.card_le_card_of_injective _ hf

theorem le_iSup_card_eq :
    Q ≤ ⨆ (A : Subgroup J) (_ : A ≤ Q ∧ CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 5), A := by
  obtain ⟨A1, hA1Q, hA1, hA1c, hA1m⟩ := exists_elemAbelian genB1 genB1_bil genB1_qf genB1_inj
  obtain ⟨A2, hA2Q, hA2, hA2c, hA2m⟩ := exists_elemAbelian genB2 genB2_bil genB2_qf genB2_inj
  have hQ : Q ≤ A1 ⊔ A2 := by
    refine (Subgroup.closure_le _).2 fun g hg => SetLike.mem_coe.2 ?_
    rcases hg with rfl | ⟨i, rfl⟩
    · have e : ExtraspecialNF.nf z q 1 (lc genB1 0) = z := by
        rw [show lc genB1 0 = 0 from funext fun k => by simp [lc]]
        exact ExtraspecialNF.nf_one_zero z q
      rw [← e]
      exact Subgroup.mem_sup_left (hA1m 1 0)
    · obtain ⟨u, v, huv⟩ := genB_span i
      have e := ExtraspecialNF.nf_mul_nf symplectic_rel 0
        (ExtraspecialNF.collect c (lc genB1 u) (lc genB2 v)) (lc genB1 u) (lc genB2 v)
      have h0 : (0 : ZMod 2) + ExtraspecialNF.collect c (lc genB1 u) (lc genB2 v) +
          ExtraspecialNF.collect c (lc genB1 u) (lc genB2 v) = 0 := by
        generalize ExtraspecialNF.collect c (lc genB1 u) (lc genB2 v) = a
        revert a
        decide
      rw [h0, ← huv, ExtraspecialNF.nf_single] at e
      rw [← e]
      exact (A1 ⊔ A2).mul_mem (Subgroup.mem_sup_left (hA1m 0 u))
        (Subgroup.mem_sup_right (hA2m _ v))
  exact hQ.trans (sup_le (le_iSup₂_of_le A1 ⟨hA1Q, hA1, hA1c⟩ le_rfl)
    (le_iSup₂_of_le A2 ⟨hA2Q, hA2, hA2c⟩ le_rfl))

end CFSG.Sporadic.Th.Max3.Rank
