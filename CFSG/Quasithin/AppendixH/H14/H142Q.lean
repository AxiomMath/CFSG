module

public import CFSG.Quasithin.AppendixH.H14.H142QData
public import CFSG.Quasithin.AppendixH.H14.H142Card
public import CFSG.Quasithin.AppendixH.H14.H142Group
public import CFSG.Quasithin.AppendixH.H14.H142Conj

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Open
open scoped Pointwise

@[expose] def stdMQ : Subgroup S24 := M23g 8 ⊓ MulAction.stabilizer S24 stdQ

@[expose] noncomputable def stdEQ : Subgroup S24 := tabSub qTabArr qTab_ok

@[expose] noncomputable def qRep (k : ℕ) : S24 := permOfArrD qReps[k]!

@[expose] noncomputable def qGenPerm (j : ℕ) : S24 := permOfArrD qGens[j]!

theorem card_stdEQ : Nat.card ↥stdEQ = 16 := card_tabSub qTab_ok

theorem isElemAbelian_stdEQ : IsElemAbelian 2 stdEQ := isElemAbelian_tabSub qTab_ok

theorem isPGroup_stdEQ : IsPGroup 2 stdEQ := isPGroup_tabSub qTab_ok

theorem stdEQ_ne_bot : stdEQ ≠ ⊥ := tabSub_ne_bot qTab_ok

theorem stdEQ_le_stdMQ : stdEQ ≤ stdMQ := by
  intro x hx
  rw [stdEQ, mem_tabSub] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hspec := (tabOK_spec qTab_ok).2 n hn
  have hstab := qTab_stab n hn
  have harr := hasArr_tabPerm qTab_ok hn
  rw [stdMQ, Subgroup.mem_inf]
  exact ⟨mem_M23g_of_arr harr hspec.1 8 hstab.1,
    by rw [MulAction.mem_stabilizer_iff]; exact smul_stdQ_of_arr harr hstab.2⟩

theorem qGenPerm_spec {j : ℕ} (hj : j < 2) :
    inAutOK qGens[j]! = true ∧ HasArr (qGenPerm j) qGens[j]! ∧ qGenPerm j ∈ stdMQ := by
  have hmem : qGens[j]! ∈ qGens := by
    interval_cases j <;> decide
  obtain ⟨hok, h8, hmask⟩ := qGens_ok (qGens[j]!) hmem
  have harr : HasArr (qGenPerm j) qGens[j]! := by
    rw [qGenPerm]; exact hasArr_permOfArrD hok
  refine ⟨hok, harr, ?_⟩
  rw [stdMQ, Subgroup.mem_inf]
  exact ⟨mem_M23g_of_arr harr hok 8 h8,
    by rw [MulAction.mem_stabilizer_iff]; exact smul_stdQ_of_arr harr hmask⟩

theorem qGens_mem : ∀ a ∈ qGens, inAutOK a = true ∧ ∃ σ ∈ stdMQ, HasArr σ a := by
  intro a ha
  have hcases : a = qGens[0]! ∨ a = qGens[1]! := by
    obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp ha
    have hj2 : j < 2 := by
      have hlen : qGens.length = 2 := by decide
      rw [hlen] at hj; exact hj
    interval_cases j
    · left; rw [← hja]; rfl
    · right; rw [← hja]; rfl
  rcases hcases with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := qGenPerm_spec (j := 0) (by norm_num)
    exact ⟨h1, qGenPerm 0, h3, h2⟩
  · obtain ⟨h1, h2, h3⟩ := qGenPerm_spec (j := 1) (by norm_num)
    exact ⟨h1, qGenPerm 1, h3, h2⟩

theorem qRep_spec {k : ℕ} (hk : k < 360) : HasArr (qRep k) qReps[k]! ∧ qRep k ∈ stdMQ := by
  obtain ⟨hok, h8, hmask⟩ := qReps_ok k hk
  have harr : HasArr (qRep k) qReps[k]! := by
    rw [qRep]; exact hasArr_permOfArrD hok
  refine ⟨harr, ?_⟩
  rw [stdMQ, Subgroup.mem_inf]
  exact ⟨mem_M23g_of_arr harr hok 8 h8,
    by rw [MulAction.mem_stabilizer_iff]; exact smul_stdQ_of_arr harr hmask⟩

theorem qRep_zero : qRep 0 = 1 := by
  have h := (qRep_spec (k := 0) (by norm_num)).1
  rw [qBfs_ok.1] at h
  exact hasArr_unique h hasArr_one

theorem qRep_succ {k : ℕ} (hk : k < 360) (hk0 : 0 < k) :
    qRep k = qGenPerm (qGen k) * qRep (qPar k) := by
  obtain ⟨hpar, hgen, hbfs⟩ := qBfs_ok.2 k hk hk0
  have hpar360 : qPar k < 360 := hpar.trans hk
  have hgarr := (qGenPerm_spec hgen).2.1
  have hrarr := (qRep_spec hpar360).1
  have hprod : HasArr (qGenPerm (qGen k) * qRep (qPar k))
      (comp24 qGens[qGen k]! qReps[qPar k]!) := hasArr_mul hgarr hrarr
  rw [← hbfs] at hprod
  exact hasArr_unique (qRep_spec hk).1 hprod

theorem qGenPerm_conj {j : ℕ} (hj : j < 2) {m : ℕ} (hm : m < 16) :
    qGenPerm j * tabPerm qTabArr m * (qGenPerm j)⁻¹ = tabPerm qTabArr (qGMat j m) := by
  obtain ⟨hok, harr, -⟩ := qGenPerm_spec hj
  have hcmap : cmap qTabArr qGens[j]! m = qGMat j m := qGMat_eq_cmap j hj m hm
  have hlt : cmap qTabArr qGens[j]! m < 16 := by
    rw [hcmap]; exact qGMat_lt j hj m hm
  have h := conj_tabPerm qTab_ok harr hok hm hlt
  rwa [hcmap] at h

theorem qRep_conj {k : ℕ} (hk : k < 360) {n : ℕ} (hn : n < 16) :
    qRep k * tabPerm qTabArr n * (qRep k)⁻¹ = tabPerm qTabArr (qMat k n) := by
  revert hk
  refine Nat.strong_induction_on (p := fun k => k < 360 →
      qRep k * tabPerm qTabArr n * (qRep k)⁻¹ = tabPerm qTabArr (qMat k n)) k ?_
  intro j ih hj
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [qRep_zero, one_mul, inv_one, mul_one, qMats_ok.1 n hn]
  · obtain ⟨hpar, hgen, -⟩ := qBfs_ok.2 j hj hjpos
    have hpar360 : qPar j < 360 := hpar.trans hj
    have hIH := ih (qPar j) hpar hpar360
    rw [qRep_succ hj hjpos]
    calc (qGenPerm (qGen j) * qRep (qPar j)) * tabPerm qTabArr n *
            (qGenPerm (qGen j) * qRep (qPar j))⁻¹
        = qGenPerm (qGen j) * (qRep (qPar j) * tabPerm qTabArr n *
            (qRep (qPar j))⁻¹) * (qGenPerm (qGen j))⁻¹ := by group
      _ = qGenPerm (qGen j) * tabPerm qTabArr (qMat (qPar j) n) *
            (qGenPerm (qGen j))⁻¹ := by rw [hIH]
      _ = tabPerm qTabArr (qGMat (qGen j) (qMat (qPar j) n)) :=
            qGenPerm_conj hgen (qMat_lt (qPar j) hpar360 n hn)
      _ = tabPerm qTabArr (qMat j n) := by rw [← qMats_ok.2 j hj hjpos n hn]

theorem qMat_inj {k k' : ℕ} (hk : k < 360) (hk' : k' < 360)
    (h : ∀ n < 16, qMat k n = qMat k' n) : k = k' := by
  have hkL : k < qMats.length := by rw [qMats_length]; exact hk
  have hkL' : k' < qMats.length := by rw [qMats_length]; exact hk'
  have hrow : qMats[k] = qMats[k'] := by
    apply List.ext_getElem
    · rw [qMats_len16 _ (List.getElem_mem hkL), qMats_len16 _ (List.getElem_mem hkL')]
    · intro n hn hn'
      have hkn : qMat k n = qMats[k][n] := by
        rw [qMat, List.getD_eq_getElem _ _ hkL]
        exact List.getD_eq_getElem _ _ hn
      have hkn' : qMat k' n = qMats[k'][n] := by
        rw [qMat, List.getD_eq_getElem _ _ hkL']
        exact List.getD_eq_getElem _ _ hn'
      have hn16 : n < 16 := by
        rw [qMats_len16 _ (List.getElem_mem hkL)] at hn
        exact hn
      rw [← hkn, ← hkn', h n hn16]
  exact (List.Nodup.getElem_inj_iff qMats_nodup).mp hrow

theorem stdMQ_decomp :
    ∀ x ∈ stdMQ, ∃ k < 360, ∃ e ∈ stdEQ, x = qRep k * e := by
  let act : S24 → (Fin 16 → S24) := fun x n => x * tabPerm qTabArr (n : ℕ) * x⁻¹
  have hact : ∀ k : Fin 360, ∀ e ∈ stdEQ, act (qRep (k : ℕ) * e) = act (qRep (k : ℕ)) := by
    intro k e he
    rw [stdEQ, mem_tabSub] at he
    obtain ⟨m, hm, rfl⟩ := he
    funext n
    dsimp only [act]
    have hc : tabPerm qTabArr m * tabPerm qTabArr (n : ℕ) * (tabPerm qTabArr m)⁻¹
        = tabPerm qTabArr (n : ℕ) := by
      rw [tabPerm_comm qTab_ok hm n.2]
      group
    calc (qRep (k : ℕ) * tabPerm qTabArr m) * tabPerm qTabArr (n : ℕ) *
            (qRep (k : ℕ) * tabPerm qTabArr m)⁻¹
        = qRep (k : ℕ) * (tabPerm qTabArr m * tabPerm qTabArr (n : ℕ) *
            (tabPerm qTabArr m)⁻¹) * (qRep (k : ℕ))⁻¹ := by group
      _ = qRep (k : ℕ) * tabPerm qTabArr (n : ℕ) * (qRep (k : ℕ))⁻¹ := by rw [hc]
  have hinj : Function.Injective (fun k : Fin 360 => act (qRep (k : ℕ))) := by
    intro k k' hkk
    apply Fin.ext
    apply qMat_inj k.2 k'.2
    intro n hn
    have h1 : qRep (k : ℕ) * tabPerm qTabArr n * (qRep (k : ℕ))⁻¹
        = qRep (k' : ℕ) * tabPerm qTabArr n * (qRep (k' : ℕ))⁻¹ := by
      have := congrFun hkk ⟨n, hn⟩
      dsimp only [act] at this
      exact this
    have h2 : tabPerm qTabArr (qMat (k : ℕ) n) = tabPerm qTabArr (qMat (k' : ℕ) n) := by
      rw [← qRep_conj k.2 hn, ← qRep_conj k'.2 hn]
      exact h1
    exact tabPerm_inj qTab_ok (qMat_lt (k : ℕ) k.2 n hn) (qMat_lt (k' : ℕ) k'.2 n hn) h2
  have hcard : Nat.card ↥stdMQ ≤ 360 * Nat.card ↥stdEQ := by
    rw [card_stdEQ]
    norm_num
    show Nat.card ↥(M23g 8 ⊓ MulAction.stabilizer S24 stdQ) ≤ 5760
    exact card_MQ_le
  intro x hx
  obtain ⟨k, e, he, hxeq⟩ :=
    exists_mul_of_card_le (M := stdMQ) (E := stdEQ) (N := 360)
      (g := fun k : Fin 360 => qRep (k : ℕ)) (act := act)
      (fun k => (qRep_spec k.2).2) stdEQ_le_stdMQ hact hinj hcard x hx
  exact ⟨k.1, k.2, e, he, hxeq⟩

theorem stdEQ_normal :
    ∀ g ∈ stdMQ, ∀ e ∈ stdEQ, g * e * g⁻¹ ∈ stdEQ := by
  intro g hg e he
  obtain ⟨k, hk, e', he', rfl⟩ := stdMQ_decomp g hg
  rw [stdEQ] at he'
  obtain ⟨m, hm, he'eq⟩ := (mem_tabSub qTab_ok).mp he'
  subst he'eq
  rw [stdEQ, mem_tabSub] at he ⊢
  obtain ⟨n, hn, rfl⟩ := he
  refine ⟨qMat k n, qMat_lt k hk n hn, ?_⟩
  have hc : tabPerm qTabArr m * tabPerm qTabArr n * (tabPerm qTabArr m)⁻¹
      = tabPerm qTabArr n := by
    rw [tabPerm_comm qTab_ok hm hn]
    group
  calc (qRep k * tabPerm qTabArr m) * tabPerm qTabArr n * (qRep k * tabPerm qTabArr m)⁻¹
      = qRep k * (tabPerm qTabArr m * tabPerm qTabArr n * (tabPerm qTabArr m)⁻¹) *
          (qRep k)⁻¹ := by group
    _ = qRep k * tabPerm qTabArr n * (qRep k)⁻¹ := by rw [hc]
    _ = tabPerm qTabArr (qMat k n) := qRep_conj hk hn

theorem stdEQ_selfCentralizing :
    ∀ g ∈ stdMQ, (∀ e ∈ stdEQ, g * e = e * g) → g ∈ stdEQ := by
  intro g hg hcomm
  obtain ⟨k, hk, e', he', rfl⟩ := stdMQ_decomp g hg
  rw [stdEQ] at he'
  obtain ⟨m, hm, he'eq⟩ := (mem_tabSub qTab_ok).mp he'
  subst he'eq
  have hfix : ∀ n < 16, qMat k n = n := by
    intro n hn
    have he := hcomm (tabPerm qTabArr n) (tabPerm_mem_tabSub qTab_ok hn)
    have hc : tabPerm qTabArr m * tabPerm qTabArr n * (tabPerm qTabArr m)⁻¹
        = tabPerm qTabArr n := by
      rw [tabPerm_comm qTab_ok hm hn]
      group
    have hgconj : (qRep k * tabPerm qTabArr m) * tabPerm qTabArr n *
        (qRep k * tabPerm qTabArr m)⁻¹ = tabPerm qTabArr n := by
      rw [he]; group
    have hexp : (qRep k * tabPerm qTabArr m) * tabPerm qTabArr n *
        (qRep k * tabPerm qTabArr m)⁻¹ = qRep k * tabPerm qTabArr n * (qRep k)⁻¹ := by
      calc (qRep k * tabPerm qTabArr m) * tabPerm qTabArr n *
              (qRep k * tabPerm qTabArr m)⁻¹
          = qRep k * (tabPerm qTabArr m * tabPerm qTabArr n * (tabPerm qTabArr m)⁻¹) *
              (qRep k)⁻¹ := by group
        _ = qRep k * tabPerm qTabArr n * (qRep k)⁻¹ := by rw [hc]
    have hconj : qRep k * tabPerm qTabArr n * (qRep k)⁻¹ = tabPerm qTabArr n := by
      rw [← hexp]; exact hgconj
    have hpsi : tabPerm qTabArr (qMat k n) = tabPerm qTabArr n := by
      rw [← qRep_conj hk hn]; exact hconj
    exact tabPerm_inj qTab_ok (qMat_lt k hk n hn) hn hpsi
  have hk0 : k = 0 := qMat_selfC k hk hfix
  subst hk0
  rw [qRep_zero, one_mul]
  exact he'

theorem stdEQ_irreducible : ∀ W : Subgroup S24, W ≤ stdEQ → W ≠ ⊥ →
    (∀ g ∈ stdMQ, W.map (MulAut.conj g).toMonoidHom = W) → W = stdEQ := by
  have horb : ∀ n, 0 < n → n < 16 →
      ∃ g ∈ stdMQ, g * tabPerm qTabArr 1 * g⁻¹ = tabPerm qTabArr n := by
    intro n hn0 hn16
    obtain ⟨e, he, he1⟩ := qVbfs_cover n hn16 hn0
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
    obtain ⟨-, g, hg, hconj⟩ :=
      exists_conj_of_vbfs qTab_ok (hg := qGens_mem) (hL := qVbfs_ok) k hk
    refine ⟨g, hg, ?_⟩
    have hget : qVbfs.getD k (0, 0, 0) = e := by
      rw [List.getD_eq_getElem _ _ hk]
      exact hke
    rw [hget, he1] at hconj
    exact hconj
  have h := irreducible_of_orbit (tab := qTabArr) (M := stdMQ) qTab_ok
    (show tabSub qTabArr qTab_ok ≤ stdMQ from stdEQ_le_stdMQ) horb
  simpa only [stdEQ] using h

theorem pCoreOf_stdMQ : pCoreOf 2 stdMQ = stdEQ :=
  pCoreOf_eq_of_selfCentralizing_irreducible stdEQ_le_stdMQ stdEQ_normal isPGroup_stdEQ
    stdEQ_ne_bot stdEQ_selfCentralizing stdEQ_irreducible

end CFSG.Quasithin.AppendixH.H14
