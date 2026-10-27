module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSBr
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSSig

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open Certificates.Data.S1277Struct Certificates.Data.S1277Cand Certificates.Data.S1277Bfs
  Certificates.Data.S1277Sig Std

theorem sortSet_nodup (S : HashSet Nat) : (sortSet S).Nodup := by
  unfold sortSet
  have h1 : S.toList.Nodup := by
    have := HashSet.distinct_toList (m := S)
    exact List.Pairwise.imp (fun h => by simpa using h) this
  exact (List.mergeSort_perm _ _).nodup_iff.2 h1

section Cards

variable {G : Type} [Group G] {K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem KCod.card_eq (hκ : KCod K T κ) : Nat.card K = (klist T).length := by
  let f : ↥K → {n : Nat // n ∈ klist T} := fun x => ⟨κ x.1, hκ.mem x.1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (hκ.inj x.1 x.2 y.1 y.2 (congrArg Subtype.val h))
    · rintro ⟨n, hn⟩
      obtain ⟨x, hx, rfl⟩ := hκ.surj n hn
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have e2 : {n : Nat // n ∈ klist T} ≃ ↥(klist T).toFinset :=
    Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup]
  unfold klist
  exact List.nodup_range

theorem card_of_codes (hκ : KCod K T κ) (hQK : Q ≤ K) {N : List Nat} (hnd : N.Nodup)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) : Nat.card Q = N.length := by
  let f : ↥Q → {n : Nat // n ∈ N} := fun x => ⟨κ x.1, (hQN _).1 ⟨x.1, x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (hκ.inj x.1 (hQK x.2) y.1 (hQK y.2) (congrArg Subtype.val h))
    · rintro ⟨n, hn⟩
      obtain ⟨x, hx, rfl⟩ := (hQN n).2 hn
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have e2 : {n : Nat // n ∈ N} ≃ ↥N.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

end Cards

section PhiList

variable (T : KTab) (N : List Nat)

theorem phiList_nodup : (phiList T N).Nodup := sortSet_nodup _

theorem mem_phiGens_of_sq {x : Nat} (hx : x ∈ N) : mulN T x x ∈ phiGens T N := by
  unfold phiGens
  rw [mem_sortSet, mem_foldl_insert]
  right
  unfold phiGensFull
  exact List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)

theorem mem_phiGens_of_comm {x y : Nat} (hx : x ∈ N) (hy : y ∈ N) : commN T x y ∈ phiGens T N := by
  unfold phiGens
  rw [mem_sortSet, mem_foldl_insert]
  right
  unfold phiGensFull
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, List.mem_map.2 ⟨y, hy, rfl⟩⟩)

theorem mem_phiList_of_sq {x : Nat} (hx : x ∈ N) : mulN T x x ∈ phiList T N := by
  unfold phiList
  rw [mem_sortSet]
  exact mem_mulCl_of_mem T (mem_phiGens_of_sq T N hx)

theorem mem_phiList_of_comm {x y : Nat} (hx : x ∈ N) (hy : y ∈ N) :
    commN T x y ∈ phiList T N := by
  unfold phiList
  rw [mem_sortSet]
  exact mem_mulCl_of_mem T (mem_phiGens_of_comm T N hx hy)

theorem one_mem_phiList : oneN T ∈ phiList T N := by
  unfold phiList
  rw [mem_sortSet]
  exact one_mem_mulCl T _

theorem plOK_spec {Pl : List Nat} (h : plOK T Pl = true) :
    (∀ x ∈ Pl, ∀ y ∈ Pl, mulN T x y ∈ Pl) ∧ ∀ x ∈ Pl, invN T x ∈ Pl := by
  unfold plOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun x hx y hy => h.1 x hx y hy, h.2⟩

theorem frOK_spec {Pl : List Nat} {d : Nat} {tab : HashMap Nat Nat} (h : frOK T N Pl d tab = true) :
    N.length = 2 ^ d * Pl.length ∧ (∀ x ∈ N, tab.getD x 0 < 2 ^ d) ∧
      (∀ x ∈ N, ∀ y ∈ N, tab.getD (mulN T x y) 0 = (tab.getD x 0 ^^^ tab.getD y 0)) ∧
      (∀ e < 2 ^ d, ∃ x ∈ N, tab.getD x 0 = e) ∧
      ∀ x ∈ N, (tab.getD x 0 = 0 ↔ x ∈ Pl) := by
  unfold frOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem, Bool.beq_eq_decide_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun x hx => by simpa using h2 x hx, fun x hx y hy => h3 x hx y hy,
    fun e he => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx, hxe⟩ := h4 e (List.mem_range.2 he)
    exact ⟨x, hx, by simpa using hxe⟩
  · have := h5 x hx
    simpa using this

end PhiList

section FrBuild

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem frData_of_lists (S : KSetting H K Q T κ) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) {d : Nat} {tab : HashMap Nat Nat}
    (hfr : frOK T N (phiList T N) d tab = true) (hpl : plOK T (phiList T N) = true) :
    ∃ D : FrData H Q (Phi' Q) d, ∀ x, D.wc x = tab.getD (κ x) 0 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := frOK_spec T N hfr
  obtain ⟨hmulPl, hinvPl⟩ := plOK_spec T hpl
  refine ⟨{ wc := fun g => tab.getD (κ g) 0
            hQH := S.hQK.trans S.hKH
            hNQ := Phi'_le Q
            hQn := S.hQn
            hNn := Phi'_normal S.hQn
            hcomm := fun a ha b hb => comm_mem_Phi' ha hb
            wc_lt := ?_
            wc_mul := ?_
            wc_surj := ?_
            wc_ker := ?_ }, fun x => rfl⟩
  · intro x hx
    exact f2 _ ((hQN _).1 ⟨x, hx, rfl⟩)
  · intro x hx y hy
    show tab.getD (κ (x * y)) 0 = _
    rw [S.hκ.mul x (S.hQK hx) y (S.hQK hy)]
    exact f3 _ ((hQN _).1 ⟨x, hx, rfl⟩) _ ((hQN _).1 ⟨y, hy, rfl⟩)
  · intro e he
    obtain ⟨n, hn, hne⟩ := f4 e he
    obtain ⟨q, hq, rfl⟩ := (hQN n).2 hn
    exact ⟨q, hq, hne⟩
  · intro x hx
    show tab.getD (κ x) 0 = 0 ↔ x ∈ Phi' Q
    rw [f5 _ ((hQN _).1 ⟨x, hx, rfl⟩)]
    constructor
    · intro hxPl
      obtain ⟨r, hr, hrκ⟩ := Phi'_codes_ge S.hκ S.hinv S.hQK hQN (κ x)
        (by unfold phiList at hxPl; rwa [mem_sortSet] at hxPl)
      have := S.hκ.inj r (S.hQK (Phi'_le Q hr)) x (S.hQK hx) hrκ
      rw [← this]; exact hr
    · intro hxΦ
      exact Phi'_codes_le S.hκ S.hinv S.hQK hQN (fun x hx => mem_phiList_of_sq T N hx)
        (fun x hx y hy => mem_phiList_of_comm T N hx hy) hmulPl (one_mem_phiList T N) hinvPl
        x hxΦ

end FrBuild

section Labels

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

open scoped Classical in
noncomputable def lamOf (z : G) (Q : Subgroup G) (typ : Nat) (x : G) : Nat :=
  if typ = 0 then (if x = z then 1 else 0)
  else if typ = 1 then (if x * x = 1 then 0 else 1)
  else (if ∀ n ∈ Phi' Q, x * n = n * x then 1 else 0)

theorem mem_phiList_iff (S : KSetting H K Q T κ) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hpl : plOK T (phiList T N) = true) (p : Nat) :
    p ∈ phiList T N ↔ ∃ r ∈ Phi' Q, κ r = p := by
  obtain ⟨hmulPl, hinvPl⟩ := plOK_spec T hpl
  constructor
  · intro hp
    exact Phi'_codes_ge S.hκ S.hinv S.hQK hQN p (by unfold phiList at hp; rwa [mem_sortSet] at hp)
  · rintro ⟨r, hr, rfl⟩
    exact Phi'_codes_le S.hκ S.hinv S.hQK hQN (fun x hx => mem_phiList_of_sq T N hx)
      (fun x hx y hy => mem_phiList_of_comm T N hx hy) hmulPl (one_mem_phiList T N) hinvPl r hr

theorem labelOf_eq (S : KSetting H K Q T κ) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hpl : plOK T (phiList T N) = true)
    {z : G} (hzK : z ∈ K) {zN : Nat} (hκz : κ z = zN) (typ : Nat) {x : G} (hx : x ∈ Q) :
    labelOf T zN (phiList T N) typ (κ x) = lamOf z Q typ x := by
  classical
  have hxK : x ∈ K := S.hQK hx
  unfold labelOf lamOf
  by_cases h0 : typ = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hxz : x = z
    · subst hxz; simp [hκz]
    · have : κ x ≠ zN := fun h => hxz (S.hκ.inj x hxK z hzK (h.trans hκz.symm))
      simp [hxz, this]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : typ = 1
    · rw [if_pos h1, if_pos h1]
      have e : mulN T (κ x) (κ x) = κ (x * x) := (S.hκ.mul x hxK x hxK).symm
      by_cases hxx : x * x = 1
      · simp [e, hxx, S.hκ.one]
      · have : κ (x * x) ≠ oneN T := by
          rw [← S.hκ.one]
          exact fun h => hxx (S.hκ.inj _ (K.mul_mem hxK hxK) 1 K.one_mem h)
        simp [e, hxx, this]
    · rw [if_neg h1, if_neg h1]
      have hiff : (∀ p ∈ phiList T N, mulN T (κ x) p = mulN T p (κ x)) ↔
          ∀ n ∈ Phi' Q, x * n = n * x := by
        constructor
        · intro h n hn
          have hnK : n ∈ K := S.hQK (Phi'_le Q hn)
          have := h (κ n) ((mem_phiList_iff S hQN hpl _).2 ⟨n, hn, rfl⟩)
          rw [← S.hκ.mul x hxK n hnK, ← S.hκ.mul n hnK x hxK] at this
          exact S.hκ.inj _ (K.mul_mem hxK hnK) _ (K.mul_mem hnK hxK) this
        · intro h p hp
          obtain ⟨n, hn, rfl⟩ := (mem_phiList_iff S hQN hpl p).1 hp
          have hnK : n ∈ K := S.hQK (Phi'_le Q hn)
          rw [← S.hκ.mul x hxK n hnK, ← S.hκ.mul n hnK x hxK, h n hn]
      have hcond : ((phiList T N).all (fun p => mulN T (κ x) p == mulN T p (κ x)) = true) ↔
          ∀ n ∈ Phi' Q, x * n = n * x := by
        simp only [List.all_eq_true, beq_iff_eq]
        exact hiff
      exact if_congr hcond rfl rfl

theorem lamOf_inv {z : G} (hzH : ∀ h ∈ H, h * z * h⁻¹ = z)
    (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) (typ : Nat) {h : G} (hh : h ∈ H) {x : G}
    (hx : x ∈ Q) : lamOf z Q typ (h * x * h⁻¹) = lamOf z Q typ x := by
  classical
  unfold lamOf
  by_cases h0 : typ = 0
  · rw [if_pos h0, if_pos h0]
    have hiff : (h * x * h⁻¹ = z) ↔ x = z := by
      constructor
      · intro e
        have : x = h⁻¹ * (h * x * h⁻¹) * h := by group
        rw [this, e]
        have := hzH h⁻¹ (H.inv_mem hh)
        simpa using this
      · rintro rfl; exact hzH h hh
    exact if_congr hiff rfl rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : typ = 1
    · rw [if_pos h1, if_pos h1]
      have e : (h * x * h⁻¹) * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
      have hiff : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 ↔ x * x = 1 := by
        rw [e]
        constructor
        · intro e'
          have : x * x = h⁻¹ * (h * (x * x) * h⁻¹) * h := by group
          rw [this, e']; group
        · intro e'; rw [e']; group
      exact if_congr hiff rfl rfl
    · rw [if_neg h1, if_neg h1]
      have hiff : (∀ n ∈ Phi' Q, h * x * h⁻¹ * n = n * (h * x * h⁻¹)) ↔
          ∀ n ∈ Phi' Q, x * n = n * x := by
        constructor
        · intro hc n' hn'
          have hn := Phi'_normal hQn h hh n' hn'
          have := hc _ hn
          have e1 : h * x * h⁻¹ * (h * n' * h⁻¹) = h * (x * n') * h⁻¹ := by group
          have e2 : h * n' * h⁻¹ * (h * x * h⁻¹) = h * (n' * x) * h⁻¹ := by group
          rw [e1, e2] at this
          exact mul_left_cancel (mul_right_cancel this)
        · intro hc n hn
          have hn' : h⁻¹ * n * h ∈ Phi' Q := by
            have := Phi'_normal hQn h⁻¹ (H.inv_mem hh) n hn
            simpa using this
          have := hc _ hn'
          have e1 : h * x * h⁻¹ * n = h * (x * (h⁻¹ * n * h)) * h⁻¹ := by group
          have e2 : n * (h * x * h⁻¹) = h * ((h⁻¹ * n * h) * x) * h⁻¹ := by group
          rw [e1, e2, this]
      exact if_congr hiff rfl rfl

end Labels

section XPart

theorem xOK_spec {d : Nat} {sl Xl : List (List Nat)} (h : xOK d sl Xl = true) :
    (∀ x ∈ Xl, x ∈ sl) ∧ idCols d ∈ Xl ∧ (∀ x ∈ Xl, ∀ y ∈ Xl, compCols x y ∈ Xl) ∧
      (∀ x ∈ Xl, compCols x x = idCols d) ∧
      (∀ σ ∈ sl, ∀ x ∈ Xl, ∃ y ∈ Xl, compCols σ x = compCols y σ) ∧ 8 ≤ Xl.length := by
  unfold xOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨fun x hx => h1 x hx, h2, fun x hx y hy => h3 x hx y hy, fun x hx => h4 x hx,
    fun σ hσ x hx => h5 σ hσ x hx, h6⟩

theorem exists_X {d : Nat} {φ : Nat → Nat} {Xl : List (List Nat)} (hnd : Xl.Nodup)
    (h : xOK d (sigList d φ) Xl = true) :
    ∃ X : Subgroup (Equiv.Perm (Fin (2 ^ d))), X ≤ Sig d φ ∧
      (∀ τ ∈ Sig d φ, ∀ x ∈ X, τ * x * τ⁻¹ ∈ X) ∧ IsPGroup 2 ↥X ∧ 8 ≤ Nat.card X := by
  classical
  obtain ⟨hsub, hid, hmul, hsq, hnorm, hlen⟩ := xOK_spec h
  have hreal : ∀ y ∈ Xl, ∃ σ ∈ Sig d φ, colsOf σ = y := fun y hy =>
    exists_of_mem_sigList (hsub y hy)
  have hsq' : ∀ σ ∈ Sig d φ, colsOf σ ∈ Xl → σ * σ = 1 := by
    intro σ hσ hc
    apply colsOf_injective ((Sig d φ).mul_mem hσ hσ) (Sig d φ).one_mem
    rw [colsOf_mul hσ.1, colsOf_one]
    exact hsq _ hc
  let X : Subgroup (Equiv.Perm (Fin (2 ^ d))) :=
    { carrier := {σ | σ ∈ Sig d φ ∧ colsOf σ ∈ Xl}
      one_mem' := ⟨(Sig d φ).one_mem, by rw [colsOf_one]; exact hid⟩
      mul_mem' := fun {σ τ} hσ hτ => ⟨(Sig d φ).mul_mem hσ.1 hτ.1, by
        rw [colsOf_mul hσ.1.1]; exact hmul _ hσ.2 _ hτ.2⟩
      inv_mem' := fun {σ} hσ => by
        have : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (hsq' σ hσ.1 hσ.2)
        rw [this]; exact hσ }
  refine ⟨X, fun σ hσ => hσ.1, ?_, ?_, ?_⟩
  · intro τ hτ σ hσ
    obtain ⟨y, hy, hcomm⟩ := hnorm (colsOf τ) (colsOf_mem_sigList hτ) _ hσ.2
    obtain ⟨y', hy'S, rfl⟩ := hreal y hy
    have h1 : colsOf (τ * σ) = colsOf (y' * τ) := by
      rw [colsOf_mul hτ.1, colsOf_mul hy'S.1]; exact hcomm
    have h2 : τ * σ = y' * τ :=
      colsOf_injective ((Sig d φ).mul_mem hτ hσ.1) ((Sig d φ).mul_mem hy'S hτ) h1
    have : τ * σ * τ⁻¹ = y' := by rw [h2]; group
    rw [this]
    exact ⟨hy'S, hy⟩
  · intro σ
    refine ⟨1, Subtype.ext ?_⟩
    show (σ : Equiv.Perm (Fin (2 ^ d))) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact hsq' σ.1 σ.2.1 σ.2.2
  ·
    let f : {y // y ∈ Xl} → ↥X := fun y => ⟨(hreal y.1 y.2).choose, (hreal y.1 y.2).choose_spec.1,
      by rw [(hreal y.1 y.2).choose_spec.2]; exact y.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have := congrArg (fun x : ↥X => colsOf x.1) hab
      simp only [f] at this
      rw [(hreal a.1 a.2).choose_spec.2, (hreal b.1 b.2).choose_spec.2] at this
      exact this
    have h1 := Nat.card_le_card_of_injective f hf
    have e2 : {y // y ∈ Xl} ≃ ↥Xl.toFinset := Equiv.subtypeEquivRight fun c => by simp
    rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd] at h1
    omega

end XPart

theorem card_le_relIndex_of_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {X R P : Subgroup Γ}
    (hX : X ≤ P) (_hR : R ≤ P) (h : X ⊓ R = ⊥) : Nat.card X ≤ R.relIndex P := by
  have hinj : Function.Injective (fun x : X =>
      (QuotientGroup.mk (⟨x.1, hX x.2⟩ : ↥P) : ↥P ⧸ R.subgroupOf P)) := by
    intro x y hxy
    have h1 := QuotientGroup.eq.1 hxy
    have h2 : x.1⁻¹ * y.1 ∈ R := Subgroup.mem_subgroupOf.1 h1
    have h3 : x.1⁻¹ * y.1 ∈ X := X.mul_mem (X.inv_mem x.2) y.2
    have h4 : x.1⁻¹ * y.1 ∈ X ⊓ R := ⟨h3, h2⟩
    rw [h, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  exact Nat.card_le_card_of_injective _ hinj


section BranchSig

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem sigOK_unfold {T : KTab} {Olist N : List Nat} {zN : Nat} (h : sigOK T Olist N zN = true) :
    ∃ (Pl : List Nat) (d typ : Nat) (tab : HashMap Nat Nat) (pt : List Nat),
      Pl = phiList T N ∧ pt = phiTab T zN Pl N typ d tab ∧
      sigCheck T Olist N zN Pl d typ tab pt (sigList d (phiFn pt)) = true :=
  ⟨_, _, _, _, _, rfl, rfl, h⟩

theorem sigCheck_spec {T : KTab} {Olist N : List Nat} {zN : Nat} {Pl : List Nat} {d typ : Nat}
    {tab : HashMap Nat Nat} {pt : List Nat} {sl : List (List Nat)}
    (h : sigCheck T Olist N zN Pl d typ tab pt sl = true) :
    plOK T Pl = true ∧ frOK T N Pl d tab = true ∧ phiOK T zN Pl N typ d tab = true ∧
      N.length * ((klist T).length / N.length) = (klist T).length ∧
      sl.length % ((klist T).length / N.length) = 0 ∧
      ((∃ k, k < 20 ∧ sl.length / ((klist T).length / N.length) = 3 * 2 ^ k) ∧
          4 * N.length ≤ Olist.length ∨
        (∃ k, k < 3 ∧ sl.length / ((klist T).length / N.length) = 7 * 2 ^ k) ∧
          xOK d sl (xList d sl (tab.getD zN 0)) = true) := by
  unfold sigCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with ⟨⟨k, hk, hk'⟩, h7⟩ | ⟨⟨k, hk, hk'⟩, h7⟩
  · exact Or.inl ⟨⟨k, hk, hk'⟩, h7⟩
  · exact Or.inr ⟨⟨k, hk, hk'⟩, h7⟩

theorem branch_sig (S : KSetting H K Q T κ) {z : G} (hzH : ∀ h ∈ H, h * z * h⁻¹ = z)
    (hzK : z ∈ K) {zN : Nat} (hκz : κ z = zN) {N Olist : List Nat} (hNnd : N.Nodup)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hQeq : Q = pCoreOf 2 H)
    (hO : ∃ O : Subgroup G, O ≤ K ∧ (∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O) ∧ IsPGroup 2 ↥O ∧
      Olist.length ≤ Nat.card ↥O)
    (hsig : sigOK T Olist N zN = true) : False := by
  classical
  obtain ⟨Pl, d, typ, tab, pt, hPl, hpt, hchk⟩ := sigOK_unfold hsig
  obtain ⟨hpl, hfr, hphiOK, harith1, harith2, harith3⟩ := sigCheck_spec hchk
  subst hPl
  obtain ⟨D, hD⟩ := frData_of_lists S hQN hfr hpl
  have hphi : ∀ x ∈ Q, phiFn pt (D.wc x) = lamOf z Q typ x := by
    intro x hx
    have hxN : κ x ∈ N := (hQN _).1 ⟨x, hx, rfl⟩
    have h1 := (List.all_eq_true.1 (by
      have := hphiOK
      unfold phiOK at this
      rw [← hpt] at this
      exact this)) (κ x) hxN
    rw [beq_iff_eq] at h1
    rw [hD x, h1]
    exact labelOf_eq S hQN hpl hzK hκz typ hx
  have hlam : ∀ h ∈ H, ∀ x ∈ Q, lamOf z Q typ (h * x * h⁻¹) = lamOf z Q typ x :=
    fun h hh x hx => lamOf_inv hzH S.hQn typ hh hx
  have hR : D.rho.range ≤ Sig d (phiFn pt) := D.range_le_Sig (phiFn pt) (lamOf z Q typ) hphi hlam
  have hNfr := Phi'_frattini S.hQ2
  have hcardH : Nat.card H = Nat.card Q * Nat.card D.rho.range :=
    D.card_H S.hQmax S.hQ2 S.hC hNfr
  have hKcard : Nat.card K = (klist T).length := S.hκ.card_eq
  have hQcard : Nat.card Q = N.length := card_of_codes S.hκ S.hQK hNnd hQN
  have hm : K.relIndex H * Nat.card K = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := K) (K := H)
    rwa [inf_eq_left.2 S.hKH] at this
  have hn : 0 < N.length := by rw [← hQcard]; exact Nat.card_pos
  set n := N.length with hn_def
  set kk := (klist T).length with hkk
  set e := kk / n with he
  have hnek : n * e = kk := harith1
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exfalso
      have : kk = 0 := by rw [← hnek, h0]; simp
      have hKpos : 0 < Nat.card K := Nat.card_pos
      omega
    · exact h0
  set m := K.relIndex H with hmdef
  have hR_eq : Nat.card D.rho.range = m * e := by
    have h1 : n * Nat.card D.rho.range = n * (m * e) := by
      have a1 : Nat.card H = n * Nat.card D.rho.range := by rw [hcardH, hQcard]
      have a2 : Nat.card H = m * (n * e) := by rw [← hm, hKcard, hnek]
      calc n * Nat.card D.rho.range = m * (n * e) := a1.symm.trans a2
        _ = n * (m * e) := by ring
    exact Nat.eq_of_mul_eq_mul_left hn h1
  have hsigcard : Nat.card ↥(Sig d (phiFn pt)) = (sigList d (phiFn pt)).length := card_Sig d _
  have hdvd : m * e ∣ (sigList d (phiFn pt)).length := by
    rw [← hsigcard, ← hR_eq]
    exact Subgroup.card_dvd_of_le hR
  set s := (sigList d (phiFn pt)).length with hs
  have hse : s = e * (s / e) := by
    have := Nat.div_add_mod s e
    rw [harith2] at this; omega
  have hmdiv : m ∣ s / e := by
    have h1 : m * e ∣ e * (s / e) := by rw [← hse]; exact hdvd
    rw [mul_comm m e] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hepos h1
  have hmodd : ¬ 2 ∣ m := S.hodd
  have hm1 : m ≠ 1 := by
    intro h1
    exact S.hne (Subgroup.relIndex_eq_one.1 h1)
  have hcop : ∀ k : Nat, Nat.Coprime m (2 ^ k) := fun k =>
    Nat.Coprime.pow_right k ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hmodd)))
  rcases harith3 with ⟨⟨k, hk, hk'⟩, h4n⟩ | ⟨⟨k, hk, hk'⟩, hx⟩
  ·
    have hm3 : m ∣ 3 := by
      rw [hk'] at hmdiv
      exact (hcop k).dvd_of_dvd_mul_right hmdiv
    have hm3' : m = 3 := ((Nat.dvd_prime Nat.prime_three).1 hm3).resolve_left hm1
    obtain ⟨O, hOK, hOn, hO2, hOcard⟩ := hO
    refine no_index_three S.hKH hm3' hOK hOn hO2 ?_
    rw [← hQeq, hQcard]
    omega
  ·
    have hm7 : m ∣ 7 := by
      rw [hk'] at hmdiv
      exact (hcop k).dvd_of_dvd_mul_right hmdiv
    have hm7' : m = 7 := ((Nat.dvd_prime (by norm_num)).1 hm7).resolve_left hm1
    have hnd : (xList d (sigList d (phiFn pt)) (tab.getD zN 0)).Nodup := by
      unfold xList
      exact (sigList_nodup d _).filter _
    obtain ⟨X, hXS, hXn, hX2, hX8⟩ := exists_X hnd hx
    have hYn : ∀ r ∈ D.rho.range, ∀ y ∈ X ⊓ D.rho.range, r * y * r⁻¹ ∈ X ⊓ D.rho.range := by
      intro r hr y hy
      exact ⟨hXn r (hR hr) y hy.1, D.rho.range.mul_mem (D.rho.range.mul_mem hr hy.2)
        (D.rho.range.inv_mem hr)⟩
    have hbot : X ⊓ D.rho.range = ⊥ :=
      D.eq_bot_of_normal_two S.hQmax S.hQ2 S.hC hNfr inf_le_right hYn (hX2.to_le inf_le_left)
    have hle := card_le_relIndex_of_inf_eq_bot hXS hR hbot
    have hrel := Subgroup.relIndex_mul_card (H := D.rho.range) (K := Sig d (phiFn pt))
    rw [inf_eq_left.2 hR, hsigcard, hR_eq, hm7'] at hrel
    have h2 : D.rho.range.relIndex (Sig d (phiFn pt)) * (7 * e) = 2 ^ k * (7 * e) := by
      rw [hrel, hse, hk']; ring
    have h3 := Nat.eq_of_mul_eq_mul_right (by omega) h2
    have h4 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end BranchSig

end CFSG.Quasithin.H13.I1277

end
