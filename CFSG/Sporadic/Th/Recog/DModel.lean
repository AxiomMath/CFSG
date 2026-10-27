module

public import Certificates.Certificate687005
public import CFSG.Sporadic.Th.Recog.JLetters
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.Certificates.NormalGeneration

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords CFSG.CosetTable
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section DP

noncomputable def dP (j : Fin 6) : Equiv.Perm (Fin 51) :=
  CFSG.ONSchreier.permOfArr 51 letArr[j.val]!

@[expose] noncomputable def DP : Subgroup (Equiv.Perm (Fin 51)) :=
  Subgroup.closure (Set.range dP)

theorem dP_mem (j : Fin 6) : dP j ∈ DP := Subgroup.subset_closure ⟨j, rfl⟩

@[expose] noncomputable def dPD (j : Fin 6) : ↥DP := ⟨dP j, dP_mem j⟩

@[simp] theorem coe_dPD (j : Fin 6) : ((dPD j : ↥DP) : Equiv.Perm (Fin 51)) = dP j := rfl

theorem letArr_size_eq : letArr.size = 6 := rfl

theorem letArr_size (j : Fin 6) : letArr[j.val]!.size = 51 := by revert j; decide

theorem wTab_nil {m : ℕ} (G GI : Array Tab) : wTab G GI ([] : List (Fin m × Bool)) = idTab 51 :=
  rfl

theorem wTab_cons {m : ℕ} (G GI : Array Tab) (l : Fin m × Bool) (w : List (Fin m × Bool)) :
    wTab G GI (l :: w) = comp 51 (if l.2 then G[l.1.val]! else GI[l.1.val]!) (wTab G GI w) :=
  rfl

theorem tabRep_wTab {m : ℕ} {G GI : Array Tab} {g : Fin m → Equiv.Perm (Fin 51)}
    (hG : ∀ j, TabRep G[j.val]! (g j)) (hGI : ∀ j, TabRep GI[j.val]! (g j)⁻¹)
    (w : List (Fin m × Bool)) : TabRep (wTab G GI w) (wprod g w) := by
  induction w with
  | nil => rw [wTab_nil, wprod_nil]; exact TabRep.idTab
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [wTab_cons, wprod_cons]
    cases b
    · simpa using (hGI i).comp ih
    · simpa using (hG i).comp ih


private theorem cert_cc : Finite (PG 6 RD) ∧ Nat.card (PG 6 RD) ≤ 3456 :=
  Certificates.certificate687005.1
private theorem cert_pis (j : Fin 6) :
    CFSG.ONSchreier.Native.pisInv 51 letArr[j.val]! (letInv ())[j.val]! = true :=
  Certificates.certificate687005.2.2.1 j
private theorem cert_inv : invsOK 51 letArr (letInv ()) = true :=
  Certificates.certificate687005.2.2.2.1
private theorem cert_rd : rdCheck () = true :=
  Certificates.certificate687005.2.2.2.2.1
private theorem cert_tconj : tConjCheck () = true :=
  Certificates.certificate687005.2.2.2.2.2.1
private theorem cert_enum : enumOK 51 letArr (dEnum ()) = true :=
  Certificates.certificate687005.2.2.2.2.2.2.1
private theorem cert_size : (dEnum ()).tabs.size = 3456 :=
  Certificates.certificate687005.2.2.2.2.2.2.2.1
private theorem cert_ker : kerCheck () = true :=
  Certificates.certificate687005.2.2.2.2.2.2.2.2.1
private theorem cert_sq : (sqTabs ()).length = 164 :=
  Certificates.certificate687005.2.2.2.2.2.2.2.2.2

theorem tabRep_dP (j : Fin 6) : TabRep letArr[j.val]! (dP j) :=
  ⟨letArr_size j, (CFSG.ONSchreier.prep_permOfArr (cert_pis j)).1⟩

theorem tabRep_letInv (j : Fin 6) : TabRep (letInv ())[j.val]! (dP j)⁻¹ :=
  invsOK_spec cert_inv (by rw [letArr_size_eq]; exact j.isLt) (tabRep_dP j)

theorem enumerates_DP : Enumerates DP (dEnum ()).tabs.toList := by
  refine enumerates_closure (gens := letArr) ?_ ?_ cert_enum
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.val, by rw [letArr_size_eq]; exact j.isLt, tabRep_dP j⟩
  · intro j hj
    rw [letArr_size_eq] at hj
    exact ⟨dP ⟨j, hj⟩, ⟨⟨j, hj⟩, rfl⟩, tabRep_dP ⟨j, hj⟩⟩

theorem card_DP : Nat.card DP = 3456 := by
  rw [enumerates_DP.card, Array.length_toList, cert_size]

end DP

theorem closure_dPD : Subgroup.closure (Set.range dPD) = ⊤ := by
  have h : Subgroup.closure (((↑) : ↥DP → Equiv.Perm (Fin 51)) ⁻¹' Set.range dP) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [← h]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩

theorem DP_hom_ext {H : Type*} [Group H] {φ ψ : ↥DP →* H} (h : ∀ j, φ (dPD j) = ψ (dPD j)) :
    φ = ψ :=
  MonoidHom.eq_of_eqOn_dense closure_dPD (by rintro _ ⟨j, rfl⟩; exact h j)

section DP2


theorem rd_dPD : ∀ w ∈ RD, wprod dPD w = 1 := by
  intro w hw
  have h := cert_rd
  simp only [rdCheck, List.all_eq_true] at h
  have h1 := ((tabRep_wTab tabRep_dP tabRep_letInv w).beq_iff TabRep.idTab).1 (h w hw)
  apply Subtype.ext
  rw [show ((wprod dPD w : ↥DP) : Equiv.Perm (Fin 51)) =
    wprod (fun j => (dPD j : Equiv.Perm (Fin 51))) w from map_wprod DP.subtype dPD w]
  exact h1

theorem dPD_conj_t (j : Fin 6) :
    dPD j * dPD 5 * (dPD j)⁻¹ = dPD 5 ∨ dPD j * dPD 5 * (dPD j)⁻¹ = (dPD 5)⁻¹ := by
  have h := cert_tconj
  simp only [tConjCheck, List.all_eq_true, List.mem_finRange, forall_const] at h
  have hj := h j
  have hl := ((tabRep_dP j).comp (tabRep_dP 5)).comp (tabRep_letInv j)
  by_cases h4 : j.val = 4
  · right
    rw [if_pos (by simpa using h4)] at hj
    apply Subtype.ext
    exact (hl.beq_iff (tabRep_letInv 5)).1 hj
  · left
    rw [if_neg (by simpa using h4)] at hj
    apply Subtype.ext
    exact (hl.beq_iff (tabRep_dP 5)).1 hj

theorem kerProd_cons (GI : Array Tab) (x : Tab) (ck : List (Fin 6 × Bool) × Nat)
    (L : List (List (Fin 6 × Bool) × Nat)) :
    kerProd GI x (ck :: L) =
      comp 51 (comp 51 (comp 51 (wTab letArr GI ck.1) (if ck.2 == 2 then comp 51 x x else x))
        (wTab letArr GI (FreeGroup.invRev ck.1))) (kerProd GI x L) := rfl

@[expose] noncomputable def kerElt (x : ↥DP) (L : List (List (Fin 6 × Bool) × Nat)) : ↥DP :=
  (L.map fun ck => wprod dPD ck.1 * (if ck.2 == 2 then x * x else x) * (wprod dPD ck.1)⁻¹).prod

theorem kerElt_cons (x : ↥DP) (ck : List (Fin 6 × Bool) × Nat)
    (L : List (List (Fin 6 × Bool) × Nat)) :
    kerElt x (ck :: L) =
      wprod dPD ck.1 * (if ck.2 == 2 then x * x else x) * (wprod dPD ck.1)⁻¹ * kerElt x L := rfl

theorem tabRep_kerProd {xt : Tab} {x : ↥DP} (hx : TabRep xt (x : Equiv.Perm (Fin 51)))
    (L : List (List (Fin 6 × Bool) × Nat)) :
    TabRep (kerProd (letInv ()) xt L) (kerElt x L : Equiv.Perm (Fin 51)) := by
  induction L with
  | nil => exact TabRep.idTab
  | cons ck L ih =>
    rw [kerProd_cons, kerElt_cons, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, show ((wprod dPD ck.1 : ↥DP) : Equiv.Perm (Fin 51)) = wprod dP ck.1 from
        map_wprod DP.subtype dPD ck.1]
    have hc := tabRep_wTab tabRep_dP tabRep_letInv ck.1
    have hci := tabRep_wTab tabRep_dP tabRep_letInv (FreeGroup.invRev ck.1)
    rw [wprod_invRev] at hci
    have hxk : TabRep (if ck.2 == 2 then comp 51 xt xt else xt)
        ((if ck.2 == 2 then x * x else x : ↥DP) : Equiv.Perm (Fin 51)) := by
      split_ifs
      · exact hx.comp hx
      · exact hx
    exact ((hc.comp hxk).comp hci).comp ih

theorem kerElt_mem {N : Subgroup ↥DP} [hN : N.Normal] {x : ↥DP} (hx : x ∈ N)
    (L : List (List (Fin 6 × Bool) × Nat)) : kerElt x L ∈ N := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨ck, -, rfl⟩ := List.mem_map.1 hy
  apply hN.conj_mem
  split_ifs
  · exact N.mul_mem hx hx
  · exact hx

theorem tabRep_targetTab (k : ℕ) :
    TabRep (targetTab (letInv ()) k)
      (if k == 0 then dP 0 else if k == 1 then dP 5 else (dP 5)⁻¹) := by
  unfold targetTab
  split_ifs
  · exact tabRep_dP 0
  · exact tabRep_dP 5
  · exact tabRep_letInv 5

theorem prime_dvd_3456 {p : ℕ} (hp : p.Prime) (h : p ∣ 3456) : p = 2 ∨ p = 3 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 3 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3))

theorem a_or_t_mem_of_ne_bot (N : Subgroup ↥DP) [hNn : N.Normal] (hN : N ≠ ⊥) :
    dPD 0 ∈ N ∨ dPD 5 ∈ N := by
  obtain ⟨p, x, hp, hpd, hxN, hxo⟩ := CFSG.Certificates.exists_prime_order_mem_subgroup N hN
  rw [card_DP] at hpd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  obtain ⟨i, hi, hrep⟩ := enumerates_DP.exists_pos x.2
  have hk := cert_ker
  simp only [kerCheck, Bool.and_eq_true, allBelow_eq_true] at hk
  obtain ⟨hroots, hall⟩ := hk
  have hi' := hall i hi
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', anyBelow_eq_true] at hi'
  rcases hi' with (h1 | ⟨h2, h3⟩) | ⟨r, hr, hf⟩
  · exact absurd (Subtype.ext ((hrep.beq_iff TabRep.idTab).1 h1)) hx1
  · exfalso
    rcases prime_dvd_3456 hp hpd with rfl | rfl
    · have h : (x : Equiv.Perm (Fin 51)) * x = 1 := by
        have := congrArg Subtype.val hxp
        simpa [pow_two] using this
      rw [← (hrep.comp hrep).beq_iff TabRep.idTab] at h
      rw [h] at h2
      exact Bool.noConfusion h2
    · have h : (x : Equiv.Perm (Fin 51)) * (x * x) = 1 := by
        have := congrArg Subtype.val hxp
        simpa [pow_succ, mul_assoc] using this
      rw [← (hrep.comp (hrep.comp hrep)).beq_iff TabRep.idTab] at h
      rw [h] at h3
      exact Bool.noConfusion h3
  · obtain ⟨hor, hw⟩ := hroots r hr
    have hroot := tabRep_wTab tabRep_dP tabRep_letInv (primeReps.getD r [])
    obtain ⟨hcl, -, -⟩ := conj_orbit (A := Set.range dP) (gens := letArr) (ginv := letInv ())
      (by
        rintro _ ⟨j, rfl⟩
        exact ⟨j.val, by rw [letArr_size_eq]; exact j.isLt, tabRep_dP j⟩)
      (by
        intro j hj
        rw [letArr_size_eq] at hj
        exact ⟨dP ⟨j, hj⟩, ⟨⟨j, hj⟩, rfl⟩, tabRep_dP ⟨j, hj⟩⟩) hroot hor
    obtain ⟨c, hc, hcr⟩ := hcl _ (mem_of_found hf)
    have hxc := hrep.perm_eq hcr
    set x₀ : ↥DP := wprod dPD (primeReps.getD r []) with hx₀def
    have hx₀ : (x₀ : Equiv.Perm (Fin 51)) = wprod dP (primeReps.getD r []) :=
      map_wprod DP.subtype dPD _
    have hx₀N : x₀ ∈ N := by
      have hcD : (⟨c, hc⟩ : ↥DP)⁻¹ * x * ⟨c, hc⟩ = x₀ := by
        apply Subtype.ext
        simp [hxc, hx₀, mul_assoc]
      rw [← hcD]
      simpa using hNn.conj_mem x hxN (⟨c, hc⟩ : ↥DP)⁻¹
    rw [← hx₀] at hroot
    simp only [kerWitOK] at hw
    have h := ((tabRep_kerProd hroot (primeWit.getD r ([], 0)).1).beq_iff
      (tabRep_targetTab (primeWit.getD r ([], 0)).2)).1 hw
    have hmem := kerElt_mem hx₀N (primeWit.getD r ([], 0)).1
    split_ifs at h
    · left
      rwa [show kerElt x₀ (primeWit.getD r ([], 0)).1 = dPD 0 from Subtype.ext h] at hmem
    · right
      rwa [show kerElt x₀ (primeWit.getD r ([], 0)).1 = dPD 5 from Subtype.ext h] at hmem
    · right
      have : kerElt x₀ (primeWit.getD r ([], 0)).1 = (dPD 5)⁻¹ := Subtype.ext h
      rw [this] at hmem
      simpa using N.inv_mem hmem

theorem card_sq_eq_one_DP : Nat.card {x : ↥DP // x ^ 2 = 1} = 164 := by
  have hE := enumerates_DP
  have hX : Nat.card {g : Equiv.Perm (Fin 51) | g ∈ DP ∧ g * g = 1} = (sqTabs ()).length := by
    apply card_set_of_tabs
    · intro t ht
      simp only [sqTabs, List.mem_filter] at ht
      obtain ⟨g, hg, hr⟩ := hE.sound t ht.1
      exact ⟨g, ⟨hg, ((hr.comp hr).beq_iff TabRep.idTab).1 ht.2⟩, hr⟩
    · rintro g ⟨hg, hgg⟩
      obtain ⟨t, ht, hr⟩ := hE.complete g hg
      exact ⟨t, List.mem_filter.2 ⟨ht, ((hr.comp hr).beq_iff TabRep.idTab).2 hgg⟩, hr⟩
    · exact hE.nodup.filter _
  rw [← cert_sq, ← hX]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, Subtype.ext ?_⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }
  · have := congrArg Subtype.val x.2
    simpa [pow_two] using this
  · simpa [pow_two] using g.2.2

theorem pgHom_dPD_bijective : Function.Bijective (pgHom dPD rd_dPD) := by
  obtain ⟨hfin, hcard⟩ := cert_cc
  have hsurj : Function.Surjective (pgHom dPD rd_dPD) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_dPD, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨PresentedGroup.of j, pgHom_of dPD rd_dPD j⟩
  exact hsurj.bijective_of_nat_card_le (hcard.trans card_DP.ge)

noncomputable def ePD : PG 6 RD ≃* ↥DP :=
  MulEquiv.ofBijective (pgHom dPD rd_dPD) pgHom_dPD_bijective

theorem ePD_of (j : Fin 6) : ePD (PresentedGroup.of j : PG 6 RD) = dPD j :=
  pgHom_of (ws := RD) dPD rd_dPD j

end DP2

section DJ


@[expose] noncomputable def dJ (j : Fin 6) : J := hswJ (dLet j)

@[expose] noncomputable def DJ : Subgroup J := Subgroup.closure (Set.range dJ)

theorem dJ_mem (j : Fin 6) : dJ j ∈ DJ := Subgroup.subset_closure ⟨j, rfl⟩

@[expose] noncomputable def dJD (j : Fin 6) : ↥DJ := ⟨dJ j, dJ_mem j⟩

@[simp] theorem coe_dJD (j : Fin 6) : ((dJD j : ↥DJ) : J) = dJ j := rfl

theorem dJ_zero : dJ 0 = (a : J) := hswJ_zero

theorem dJ_five : dJ 5 = hswJ 6 := rfl

theorem dJ_zero_ne_one : dJ 0 ≠ 1 := by
  rw [dJ_zero, ← Max3.z_eq_a]
  exact Max3.z_ne_one

theorem dJ_five_ne_one : dJ 5 ≠ 1 := by
  intro h
  have hk := kap_hswJ 6 (by decide)
  have h1 : (⟨hswJ 6, hswJ_mem_M 6 (by decide)⟩ : ↥Max3.M) = 1 := Subtype.ext h
  rw [h1, map_one, Subgroup.coe_one] at hk
  exact absurd hk.symm (by decide +kernel)

theorem closure_dJD : Subgroup.closure (Set.range dJD) = ⊤ := by
  have h : Subgroup.closure (((↑) : ↥DJ → J) ⁻¹' Set.range dJ) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [← h]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩

theorem DJ_hom_ext {H : Type*} [Group H] {φ ψ : ↥DJ →* H} (h : ∀ j, φ (dJD j) = ψ (dJD j)) :
    φ = ψ :=
  MonoidHom.eq_of_eqOn_dense closure_dJD (by rintro _ ⟨j, rfl⟩; exact h j)

theorem rd_dJ : ∀ w ∈ rdHSW, wprod dJ w = 1 := by
  intro w hw
  obtain ⟨v, hv, hren⟩ := List.mem_filterMap.1 hw
  have h := CFSG.CosetTable.map_renumber dS v w hren
  have h2 := wprod_comp_letters (fun j => dS.get j) hswJ w
  rw [h] at h2
  rw [← hswJ_rel v hv, h2]
  rfl

theorem DJ_le_M : DJ ≤ Max3.M := by
  rw [DJ, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact hswJ_mem_M (dLet j) (by revert j; decide)


theorem duSix_dJ : wprod dJ duSix = 1 := by
  have h := rowsMatrix_eq_of_eqRows Certificates.certificate687005.2.1
  rw [rowsMatrix_prodRows, rowsMatrix_idRows, List.map_replicate, rowsMatrix_mulRows,
    rowsMatrix_rowsHsw, rowsMatrix_rowsHsw, ← toMat_mul, List.prod_replicate] at h
  rw [← toMat_pow] at h
  have hrep : ∀ n : ℕ, wprod dJ (List.replicate n [((2 : Fin 6), true), (4, true)]).flatten =
      (wprod dJ [((2 : Fin 6), true), (4, true)]) ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.flatten_cons, wprod_append, ih, pow_succ']
  have h2 : wprod dJ [((2 : Fin 6), true), (4, true)] = hswJ 3 * hswJ 7 := by
    simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ↓reduceIte]
    rfl
  have hw : wprod dJ duSix = (hswJ 3 * hswJ 7) ^ 6 := by
    rw [duSix, hrep, h2]
  rw [hw]
  exact toMat_injective (h.trans toMat_one.symm)

theorem rd_dJD : ∀ w ∈ RD, wprod dJD w = 1 := by
  intro w hw
  apply Subtype.ext
  rw [show ((wprod dJD w : ↥DJ) : J) = wprod (fun j => ((dJD j : ↥DJ) : J)) w from
    map_wprod DJ.subtype dJD w]
  rcases List.mem_append.1 hw with h | h
  · exact rd_dJ w h
  · rw [List.mem_singleton.1 h]
    exact duSix_dJ

noncomputable def rhoD : ↥DP →* ↥DJ :=
  (pgHom dJD rd_dJD).comp ePD.symm.toMonoidHom

theorem rhoD_letter (j : Fin 6) : rhoD (dPD j) = dJD j := by
  have h : ePD.symm (dPD j) = (PresentedGroup.of j : PG 6 RD) := by
    rw [MulEquiv.symm_apply_eq, ePD_of]
  simp only [rhoD, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, pgHom_of]

theorem rhoD_bijective : Function.Bijective rhoD := by
  refine ⟨?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hne
    rcases a_or_t_mem_of_ne_bot rhoD.ker hne with h | h
    · exact dJ_zero_ne_one
        (congrArg Subtype.val ((MonoidHom.mem_ker.1 h).symm.trans (rhoD_letter 0)).symm)
    · exact dJ_five_ne_one
        (congrArg Subtype.val ((MonoidHom.mem_ker.1 h).symm.trans (rhoD_letter 5)).symm)
  · rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_dJD, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨dPD j, rhoD_letter j⟩

noncomputable def eDP : ↥DP ≃* ↥DJ := MulEquiv.ofBijective rhoD rhoD_bijective

theorem eDP_letter (j : Fin 6) : eDP (dPD j) = dJD j := rhoD_letter j

theorem eDP_wprod (w : List (Fin 6 × Bool)) : eDP (wprod dPD w) = wprod dJD w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wprod_cons, wprod_cons, map_mul, ih]
    split_ifs <;> simp [eDP_letter]

theorem eDP_symm_wprod (w : List (Fin 6 × Bool)) : eDP.symm (wprod dJD w) = wprod dPD w := by
  rw [MulEquiv.symm_apply_eq, eDP_wprod]

theorem coe_wprod_dJD (w : List (Fin 6 × Bool)) : ((wprod dJD w : ↥DJ) : J) = wprod dJ w :=
  map_wprod DJ.subtype dJD w

theorem dJ_conj_t (j : Fin 6) :
    dJ j * hswJ 6 * (dJ j)⁻¹ = hswJ 6 ∨ dJ j * hswJ 6 * (dJ j)⁻¹ = (hswJ 6)⁻¹ := by
  rcases dPD_conj_t j with h | h
  · left
    have := congrArg (fun x => ((eDP x : ↥DJ) : J)) h
    simpa [map_mul, map_inv, eDP_letter, coe_dJD, dJ_five] using this
  · right
    have := congrArg (fun x => ((eDP x : ↥DJ) : J)) h
    simpa [map_mul, map_inv, eDP_letter, coe_dJD, dJ_five] using this

theorem DJ_le_normalizer :
    DJ ≤ Subgroup.normalizer ((Subgroup.zpowers (hswJ 6) : Subgroup J) : Set J) := by
  rw [DJ, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  rcases dJ_conj_t j with h | h
  · exact congrArg Subgroup.zpowers h
  · show Subgroup.zpowers (dJ j * hswJ 6 * (dJ j)⁻¹) = _
    rw [h, Subgroup.zpowers_inv]

theorem card_DJ : Nat.card DJ = 3456 := by
  rw [← card_DP]
  exact Nat.card_congr eDP.symm.toEquiv

theorem card_sq_eq_one_DJ : Nat.card {x : ↥DJ // x ^ 2 = 1} = 164 := by
  rw [← card_sq_eq_one_DP]
  refine Nat.card_congr (eDP.toEquiv.subtypeEquiv fun x => ?_).symm
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]

end DJ

end CFSG.Sporadic.Th.Recog
