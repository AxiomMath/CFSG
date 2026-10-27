
module

public import Certificates.Kernel.Census.Pg.Adm
public import Certificates.Kernel.Census.Pg.ClsFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmBase
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.Misc.RuInvPack

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelPgAdm

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.W16Cls CertificateChecks.KernelPgCls
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem bind_facts : (∀ m < 60, admArr[m]! = unpack 128 8 (AK m)) ∧
    (∀ m < 60, admIso[m]! = unpack 32 7 (AI m)) ∧ (∀ a < 32, eTab[a]! = unpack 32 5 (ER a)) := by
  have h := bind_ok
  simp only [bAnd_iff, Orb.allN_iff] at h
  exact ⟨fun m hm => arrBind_sound (h.1 m hm), fun m hm => arrBind_sound (h.2.1 m hm),
    fun a ha => arrBind_sound (h.2.2 a ha)⟩

theorem mulE0_eq {a b : Nat} (ha : a < 32) (hb : b < 32) : mulE0 a b = eK a b := by
  unfold mulE0 eK
  rw [bind_facts.2.2 a ha, Orb.unpack_get hb]

theorem eK_lt (a b : Nat) : eK a b < 32 := by
  unfold eK pg
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by unfold mask; decide)

theorem mulCK_eq (a b : Nat) : mulCK a b = mulC a b := by
  unfold mulCK mulC ixPK ixP redP
  have h1 := mulE0_eq (Nat.mod_lt a (by norm_num : 0 < 32)) (Nat.mod_lt b (by norm_num : 0 < 32))
  rw [h1]
  split_ifs with h
  · rfl
  · rw [mulE0_eq (eK_lt _ _) (by unfold eT; norm_num)]

theorem fixK_succ (m p : Nat) : fixK (m + 1) 8 p =
    Nat.add (fixK m 8 p) (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pg 8 (mask 8) p m) m)) :=
  rfl

theorem fixK_eq_len (p : Nat) : ∀ m, fixK m 8 p =
    ((List.range m).filter fun c => Nat.beq (pg 8 (mask 8) p c) c).length
  | 0 => rfl
  | m + 1 => by
    rw [fixK_succ, fixK_eq_len p m, List.range_succ, List.filter_append, List.length_append]
    rcases hb : Nat.beq (pg 8 (mask 8) p m) m with _ | _ <;> simp [List.filter, hb]

theorem card_filter_fin_range' {n m : ℕ} (hm : m ≤ n) (P : Fin n → Prop) [DecidablePred P]
    (Q : ℕ → Bool) (h : ∀ c : Fin n, P c ↔ ((c : ℕ) < m ∧ Q c = true)) :
    (Finset.univ.filter P).card = ((List.range m).filter Q).length := by
  have key : (Finset.univ.filter P).card = ((Finset.range m).filter fun c => Q c = true).card := by
    refine Finset.card_bij (fun c _ => (c : ℕ)) ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [Finset.mem_filter, Finset.mem_range]
      exact (h c).1 hc
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      refine ⟨⟨b, lt_of_lt_of_le hb.1 hm⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h ⟨b, lt_of_lt_of_le hb.1 hm⟩).2 hb
  rw [key, lenFilter_range, Finset.card_filter]

theorem mi_iff {c : Nat} (hc : c < 32) : Nat.blt 0 (Nat.land MI (Nat.shiftLeft 1 c)) = true ↔
    c ≠ 0 ∧ c ≠ 21 ∧ mulC c c = 0 := by
  have h := Orb.allN_iff.1 mi_ok c hc
  rw [beq_iff_eq] at h
  rw [h]
  by_cases h0 : c = 0
  · subst h0
    simp
  · by_cases h21 : c = 21
    · subst h21
      simp
    · have e0 : Nat.beq c 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      have e21 : Nat.beq c 21 = false :=
        Bool.eq_false_iff.2 fun h => h21 (Nat.eq_of_beq_eq_true h)
      rw [e0, e21]
      simp [h0, h21]

theorem admK_iff {p : Nat} {x : Equiv.Perm (Fin 128)} (hp : PR p x) (hx : x * x = 1) :
    admK p = true ↔ AdmPred x := by
  have hpt : ∀ c (hc : c < 128), pt p c = (x ⟨c, hc⟩ : ℕ) := fun c hc => hp ⟨c, hc⟩
  have hfix : (Finset.univ.filter fun c : Fin 128 => (c : ℕ) < 32 ∧ x c = c).card = fixK 32 8 p := by
    rw [fixK_eq_len]
    refine card_filter_fin_range' (by norm_num) _ _ fun c => ?_
    rw [Nat.beq_eq, ← pt, hpt c c.2, Fin.ext_iff]
  unfold admK AdmPred
  simp only [bAnd_iff, Nat.beq_eq, Orb.allN_iff, CFSG.KC.Misc.Clos.anyN_iff, Nat.blt_eq]
  rw [hpt 32 (by norm_num), hpt 64 (by norm_num), hfix]
  constructor
  · rintro ⟨h32, h64, hE, h8, c, hc, hm, hcc⟩
    obtain ⟨m0, m21, mc⟩ := (mi_iff hc).1 (Nat.blt_eq.mpr hm)
    refine ⟨hx, h32, h64, fun d hd => ?_, h8, ⟨c, by omega⟩, hc, m0, m21, mc, ?_⟩
    · have := hE d hd
      rwa [hpt d d.2] at this
    · rw [hpt c (by omega)] at hcc
      exact Fin.ext hcc
  · rintro ⟨-, h32, h64, hE, h8, c, hc, m0, m21, mc, hcc⟩
    refine ⟨h32, h64, fun d hd => ?_, h8, (c : ℕ), hc, Nat.blt_eq.mp ((mi_iff hc).2 ⟨m0, m21, mc⟩), ?_⟩
    · rw [hpt d (by omega)]
      exact hE ⟨d, by omega⟩ hd
    · rw [hpt c c.2, hcc]

section Words

theorem sqW_iff_one' {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g)
    (hg : g ∈ Pg) : sqW w = true ↔ g * g = 1 := by
  rw [sqW_iff hw]
  constructor
  · intro h
    exact baseFaithful_Pg (g * g) (Pg.mul_mem hg hg) fun y hy => by
      rw [Equiv.Perm.mul_apply]
      exact h y hy
  · intro h x _
    have := congrArg (fun π : Equiv.Perm (Fin 128) => π x) h
    simpa [Equiv.Perm.mul_apply] using this

theorem admW_iff' {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g)
    (hg : g ∈ Pg) : admW w = true ↔ AdmPred g := by
  have h2 : (evR w 32 == 32) = true ↔ (g ⟨32, by norm_num⟩ : ℕ) = 32 := by
    rw [beq_iff_eq, evR_point hw (by norm_num : (32 : ℕ) < 128)]
  have h3 : (evR w 64 == 85) = true ↔ (g ⟨64, by norm_num⟩ : ℕ) = 85 := by
    rw [beq_iff_eq, evR_point hw (by norm_num : (64 : ℕ) < 128)]
  have h4 : ((List.range 32).all fun c => decide (evR w c < 32)) = true ↔
      ∀ c : Fin 128, (c : ℕ) < 32 → (g c : ℕ) < 32 := by
    rw [List.all_eq_true]
    constructor
    · intro h c hc
      have h' := h c (List.mem_range.2 hc)
      simp only [decide_eq_true_eq] at h'
      rw [hw c] at h'
      exact h'
    · intro h c hc
      have hc' := List.mem_range.1 hc
      simp only [decide_eq_true_eq]
      rw [evR_point hw (by omega : c < 128)]
      exact h ⟨c, by omega⟩ hc'
  have hP5 : ∀ c : Fin 128, ((c : ℕ) < 32 ∧ g c = c) ↔
      ((c : ℕ) < 32 ∧ (evR w c == c) = true) := by
    intro c
    rw [beq_iff_eq, hw c, Fin.ext_iff]
  have h5 : (((List.range 32).filter fun c => evR w c == c).length == 8) = true ↔
      (Finset.univ.filter fun c : Fin 128 => (c : ℕ) < 32 ∧ g c = c).card = 8 := by
    rw [card_filter_fin_range' (m := 32) (Q := fun c => evR w c == c) (by norm_num) _ hP5,
      beq_iff_eq]
  have h6 : ((List.range 32).any fun c => c != 0 && c != 21 && mulC c c == 0 && evR w c == c) =
      true ↔ ∃ c : Fin 128, (c : ℕ) < 32 ∧ (c : ℕ) ≠ 0 ∧ (c : ℕ) ≠ 21 ∧
        mulC (c : ℕ) (c : ℕ) = 0 ∧ g c = c := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨c, hc, hp⟩
      have hc' := List.mem_range.1 hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
      obtain ⟨⟨⟨h0, h21⟩, hm⟩, he⟩ := hp
      exact ⟨⟨c, by omega⟩, hc', h0, h21, hm,
        Fin.ext ((evR_point hw (by omega : c < 128)).symm.trans he)⟩
    · rintro ⟨c, hc, h0, h21, hm, hg'⟩
      refine ⟨(c : ℕ), List.mem_range.2 hc, ?_⟩
      have he : evR w (c : ℕ) = (c : ℕ) := (hw c).trans (congrArg Fin.val hg')
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨⟨⟨h0, h21⟩, hm⟩, he⟩
  unfold admW AdmPred
  simp only [Bool.and_eq_true]
  rw [sqW_iff_one' hw hg, h2, h3, h4, h5, h6]
  simp only [and_assoc]

end Words

@[expose] noncomputable def xA (m : Nat) : Equiv.Perm (Fin 128) := permOfArr 128 (unpack 128 8 (AK m))

theorem adm_facts {m : Nat} (hm : m < 60) : admK (AK m) = true ∧ IX m < 10575 ∧
    TT (IX m) = AK m ∧ (∀ j < m, AK m ≠ AK j) ∧ 10142 < IX m := by
  have h := Orb.allN_iff.1 adm_ok m hm
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun j hj e => ?_, Nat.blt_eq.mp (Orb.allN_iff.1 ix_ok m hm)⟩
  have := Orb.allN_iff.1 h4 j hj
  rw [e, Nat.beq_refl] at this
  exact Bool.false_ne_true this

theorem pr_xA {m : Nat} (hm : m < 60) : PR (AK m) (xA m) :=
  Orb.prep_of_rep (rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 perm_ok m hm))).1

theorem xA_cls {m : Nat} (hm : m < 60) : xA m ∈ cls 8 := by
  obtain ⟨-, h2, h3, -, h5⟩ := adm_facts hm
  refine ((cls_spec (j := 8) (by norm_num)).1 _).2 ⟨IX m - 10143, ?_, ?_⟩
  · unfold NC
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega
  · have e : Tc 8 (IX m - 10143) = AK m := by
      unfold Tc offs
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [show 10143 + (IX m - 10143) = IX m by omega, h3]
    rw [e]
    exact pr_xA hm

theorem xA_shr {m : Nat} (hm : m < 60) : AK m >>> 1024 = 0 := by
  obtain ⟨-, h2, h3, -, h5⟩ := adm_facts hm
  have h := (cls_spec (j := 8) (by norm_num)).2.2 (IX m - 10143) (by
    unfold NC
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega)
  unfold Tc offs at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  rwa [show 10143 + (IX m - 10143) = IX m by omega, h3] at h

theorem xA_mem {m : Nat} (hm : m < 60) : xA m ∈ Pg ∧ AdmPred (xA m) := by
  obtain ⟨hP, hsq, -⟩ := cls_sub (by norm_num) (xA_cls hm)
  exact ⟨hP, (admK_iff (pr_xA hm) hsq).1 (adm_facts hm).1⟩

theorem xA_inj {m m' : Nat} (hm : m < 60) (hm' : m' < 60) (e : xA m = xA m') : m = m' := by
  have h2 := pr_xA hm'
  rw [← e] at h2
  have hpr := pr_inj (pr_xA hm) h2 (xA_shr hm) (xA_shr hm')
  rcases Nat.lt_trichotomy m m' with h | h | h
  · exact absurd hpr.symm ((adm_facts hm').2.2.2.1 m h)
  · exact h
  · exact absurd hpr ((adm_facts hm).2.2.2.1 m' h)

theorem adm_xA {g : Equiv.Perm (Fin 128)} (hg : g ∈ Pg)
    (ha : AdmPred g) : ∃ m < 60, g = xA m := by
  have h1 : g * g = 1 := ha.1
  have hne : g ≠ 1 := by
    intro h
    have := ha.2.2.1
    rw [h] at this
    simp at this
  obtain ⟨j, hj, hgj⟩ := invol_cover hg hne h1
  obtain ⟨i, hi, hpi⟩ := ((cls_spec hj).1 g).1 hgj
  have hk : offs j + i < 10575 := by
    interval_cases j <;> simp only [NC, offs, List.getD_cons_succ, List.getD_cons_zero] at hi ⊢ <;>
      omega
  have hs0 := scan_ok
  unfold scanK at hs0
  have hs := Orb.allN_iff.1 hs0 (offs j + i) hk
  rw [show Nat.add 0 (offs j + i) = offs j + i from Nat.zero_add _] at hs
  change bIf(admK (TT (offs j + i)), memK 60 AK (TT (offs j + i)), true) = true at hs
  have ha' : admK (TT (offs j + i)) = true := (admK_iff hpi h1).2 ha
  rw [ha'] at hs
  change memK 60 AK (TT (offs j + i)) = true at hs
  unfold memK at hs
  obtain ⟨m, hm, he⟩ := (CFSG.KC.Misc.Clos.anyN_iff _ _).1 hs
  refine ⟨m, hm, pr_unique hpi ?_⟩
  change PR (TT (offs j + i)) (xA m)
  rw [Nat.eq_of_beq_eq_true he]
  exact pr_xA hm

theorem card_adm' : Nat.card {x : ↥Pg // AdmPred x} = 60 := by
  let F : Fin 60 → {x : ↥Pg // AdmPred (x : Equiv.Perm (Fin 128))} := fun i =>
    ⟨⟨xA i, (xA_mem i.2).1⟩, (xA_mem i.2).2⟩
  have hbij : Function.Bijective F := by
    refine ⟨fun i j hij => Fin.ext (xA_inj i.2 j.2 ?_), fun x => ?_⟩
    · exact congrArg (fun x : {x : ↥Pg // AdmPred (x : Equiv.Perm (Fin 128))} =>
        ((x.1 : ↥Pg) : Equiv.Perm (Fin 128))) hij
    · obtain ⟨m, hm, e⟩ := adm_xA x.1.2 x.2
      exact ⟨⟨m, hm⟩, Subtype.ext (Subtype.ext e.symm)⟩
  rw [← Nat.card_eq_of_bijective F hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem bIf_ct {c t : Bool} : Bool.rec (motive := fun _ => Bool) true t c = true ↔
    (c = true → t = true) := by
  cases c <;> simp

theorem foldr_count (q : Nat → Bool) : ∀ (l : List Nat) (s : Nat),
    l.foldr (fun c s => Nat.add s (Bool.rec (motive := fun _ => Nat) 0 1 (q c))) s =
      s + (l.filter q).length
  | [], s => rfl
  | c :: l, s => by
    rw [List.foldr_cons, foldr_count q l s, List.filter_cons]
    cases q c <;> simp [Nat.add_assoc]

theorem iso_of {m : Nat} (hm : m < 60) : admIsoOK m = true := by
  have h : isoK m = true := by
    by_cases h15 : m < 15
    · exact Orb.allN_iff.1 iso_ok0 m h15
    by_cases h30 : m < 30
    · have := Orb.allN_iff.1 iso_ok1 (m - 15) (by omega)
      rwa [Nat.add_eq, Nat.add_sub_cancel' (by omega : 15 ≤ m)] at this
    by_cases h45 : m < 45
    · have := Orb.allN_iff.1 iso_ok2 (m - 30) (by omega)
      rwa [Nat.add_eq, Nat.add_sub_cancel' (by omega : 30 ≤ m)] at this
    · have := Orb.allN_iff.1 iso_ok3 (m - 45) (by omega)
      rwa [Nat.add_eq, Nat.add_sub_cancel' (by omega : 45 ≤ m)] at this
  unfold isoK at h
  simp only [bAnd_iff, Nat.beq_eq, Orb.allN_iff, Nat.blt_eq] at h
  obtain ⟨f0, f21, hk, hhom, hdist, hcov, hcnt⟩ := h
  have hf : ∀ x < 32, (unpack 32 7 (AI m))[x]! = pg 7 (mask 7) (AI m) x :=
    fun x hx => Orb.unpack_get hx
  have hp : ∀ x < 128, (unpack 128 8 (AK m))[x]! = pt (AK m) x := fun x hx => Orb.unpack_get hx
  unfold admIsoOK
  rw [bind_facts.1 m hm, bind_facts.2.1 m hm]
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [unpack]
  · rw [hf 0 (by norm_num)]
    exact f0
  · rw [hf 21 (by norm_num)]
    exact f21
  · intro k hk'
    rw [hf k hk']
    obtain ⟨k1, k2⟩ := hk k hk'
    exact ⟨k1, by rw [hp _ k1]; exact k2⟩
  · intro a ha b hb
    rw [mulE0_eq ha hb, hf _ (eK_lt a b), hf a ha, hf b hb, ← mulCK_eq]
    exact hhom a ha b hb
  · intro a ha b hb
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · right
      rw [hf a ha, hf b hb]
      intro e
      have := hdist b hb a hab
      rw [e, Nat.beq_refl] at this
      exact Bool.false_ne_true this
    · left
      exact hab
    · right
      rw [hf a ha, hf b hb]
      intro e
      have := hdist a ha b hab
      rw [e, Nat.beq_refl] at this
      exact Bool.false_ne_true this
  · intro c hc
    rw [hp c hc]
    have := hcov c hc
    by_cases e : pt (AK m) c = c
    · right
      rw [e, Nat.beq_refl] at this
      obtain ⟨k, hk', hke⟩ := (CFSG.KC.Misc.Clos.anyN_iff _ _).1 this
      exact ⟨k, hk', by rw [hf k hk']; exact Nat.eq_of_beq_eq_true hke⟩
    · left
      exact e
  · rw [Orb.foldN_eq, foldr_count, Nat.zero_add] at hcnt
    refine (congrArg List.length (List.filter_congr fun c hc => ?_)).trans hcnt
    have hc' := List.mem_range.1 hc
    rw [Bool.eq_iff_iff, List.all_eq_true, Orb.allN_iff]
    constructor
    · intro hg g hg'
      have := hg g (List.mem_range.2 hg')
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
      rw [hp g hg'] at this
      rw [bIf_ct, Nat.beq_eq, Nat.beq_eq, mulCK_eq, mulCK_eq]
      intro e
      exact this.resolve_left (not_not.2 e)
    · intro hg g hg'
      have hg2 := List.mem_range.1 hg'
      have := hg g hg2
      rw [bIf_ct, Nat.beq_eq, Nat.beq_eq, mulCK_eq, mulCK_eq] at this
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      rw [hp g hg2]
      by_cases e : pt (AK m) g = g
      · exact Or.inr (this e)
      · exact Or.inl e

theorem rep_adm {m : Nat} (hm : m < 60) : Rep 128 admArr[m]! (xA m) := by
  rw [bind_facts.1 m hm]
  exact Orb.rep_unpack (pr_xA hm)

theorem facts27825 : admCheck = true := by
  classical
  unfold admCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i hi
    have hr := rep_adm hi
    obtain ⟨hP, hA⟩ := xA_mem hi
    unfold admTabOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨?_, CFSG.KC.Misc.RuInv.P.isInvA_invCand hr⟩, (inPg_iff hr).2 hP⟩,
      (admW_iff' (RepW.single hr) hP).2 hA⟩
    rw [bind_facts.1 i hi]
    simp [unpack]
  · exact fun i hi => iso_of hi
  · intro i hi j hj
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    by_cases e : i = j
    · exact Or.inl e
    · exact Or.inr (Bool.eq_false_iff.2 fun h =>
        e (xA_inj hi hj ((eqA_iff (rep_adm hi) (rep_adm hj)).1 h)))
  · rw [← card_eq_countW_Pg (f := admW) (Pr := AdmPred) fun w g hw hg => admW_iff' hw hg]
    exact card_adm'

end CertificateChecks.KernelPgAdm

end
