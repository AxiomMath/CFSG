module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux3

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem mem_normalizer_map_conj_of_commute {J : Subgroup Γ} {n c : Γ} (hnc : n * c = c * n)
    (hn : n ∈ Subgroup.normalizer (J : Set Γ)) :
    n ∈ Subgroup.normalizer ((J.map (MulAut.conj c).toMonoidHom : Subgroup Γ) : Set Γ) := by
  have hn' := L514.map_conj_eq_of_mem_normalizer hn
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have : (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      J.map (MulAut.conj c).toMonoidHom := by
    rw [L514.map_conj_map_conj, hnc, ← L514.map_conj_map_conj, hn']
  exact this

omit [Finite Γ] in
theorem stabilizer_eq {p : ℕ} {A K : Subgroup Γ} (h : DiagSetting p A K) {J J' : Subgroup Γ}
    (hJ : J ∈ lcal K) (hJ' : J' ∈ lcal K) :
    A ⊓ Subgroup.normalizer (J : Set Γ) = A ⊓ Subgroup.normalizer (J' : Set Γ) := by
  obtain ⟨c, hc, rfl⟩ := h.transitive J hJ J' hJ'
  have hcomm : ∀ n ∈ A, n * c = c * n := fun n hn =>
    (commute_of_mem h.elemAbelian.1 hn hc).eq
  ext n
  simp only [Subgroup.mem_inf]
  refine and_congr_right fun hnA => ⟨fun hn => mem_normalizer_map_conj_of_commute (hcomm n hnA) hn,
    fun hn => ?_⟩
  have := mem_normalizer_map_conj_of_commute (J := J.map (MulAut.conj c).toMonoidHom)
    (n := n) (c := c⁻¹) (by
      have h1 := hcomm n hnA
      calc n * c⁻¹ = c⁻¹ * (c * n) * c⁻¹ := by group
        _ = c⁻¹ * (n * c) * c⁻¹ := by rw [h1]
        _ = c⁻¹ * n := by group) hn
  rwa [L514.map_conj_map_conj, inv_mul_cancel, Diag.map_conj_one] at this

omit [Finite Γ] in
theorem centralizer_le_normalizer_of_mem_lcal {K J : Subgroup Γ} (hJ : J ∈ lcal K) :
    Subgroup.centralizer (K : Set Γ) ≤ Subgroup.normalizer (J : Set Γ) :=
  (Subgroup.centralizer_le (fun _ hx => (mem_lcal_iff.mp hJ).1 hx)).trans
    (Subgroup.centralizer_le_normalizer _)

omit [Finite Γ] in
theorem mem_centralizer_of_centralizes_component {p : ℕ} {A K : Subgroup Γ} (h : DiagSetting p A K)
    {J : Subgroup Γ} (hJ : J ∈ lcal K) {n : Γ} (hnA : n ∈ A)
    (hn : n ∈ Subgroup.centralizer (J : Set Γ)) : n ∈ Subgroup.centralizer (K : Set Γ) := by
  have hKle : K ≤ Subgroup.centralizer ({n} : Set Γ) := by
    rw [← h.direct.sSup_eq]
    refine sSup_le fun J' hJ' => ?_
    obtain ⟨c, hc, rfl⟩ := h.transitive J hJ J' hJ'
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hnc : n * c = c * n := (commute_of_mem h.elemAbelian.1 hnA hc).eq
    have hnx : n * x = x * n := (Subgroup.mem_centralizer_iff.mp hn x hx).symm
    show (MulAut.conj c) x * n = n * (MulAut.conj c) x
    simp only [MulAut.conj_apply]
    calc c * x * c⁻¹ * n = c * x * (c⁻¹ * n) := by group
      _ = c * x * (n * c⁻¹) := by
        have : c⁻¹ * n = n * c⁻¹ := by
          have h2 := congrArg (fun z => c⁻¹ * z * c⁻¹) hnc
          simpa [mul_assoc] using h2
        rw [this]
      _ = c * (x * n) * c⁻¹ := by group
      _ = c * (n * x) * c⁻¹ := by rw [hnx]
      _ = (c * n) * x * c⁻¹ := by group
      _ = (n * c) * x * c⁻¹ := by rw [hnc]
      _ = n * (c * x * c⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hKle hk)

theorem mem_sup_of_centralizer_le {p : ℕ} {A K : Subgroup Γ} (h : DiagSetting p A K)
    {N : Subgroup Γ} (hN : ∀ J ∈ lcal K, N = A ⊓ Subgroup.normalizer (J : Set Γ)) {a b : Γ}
    (ha : a ∈ A) (hb : b ∈ A) (haN : a ∉ N)
    (hle : K ⊓ Subgroup.centralizer {a} ≤ Subgroup.centralizer {b}) :
    b ∈ (A ⊓ Subgroup.centralizer (K : Set Γ)) ⊔ Subgroup.zpowers a := by
  have hp := h.prime
  have hK := h.direct
  have hap : a ^ p = 1 := h.elemAbelian.2 a ha
  have haK : a ∈ Subgroup.normalizer (K : Set Γ) := h.normalizes ha
  have haJ : ∀ J ∈ lcal K, a ∉ Subgroup.normalizer (J : Set Γ) := fun J hJ hJa =>
    haN ((hN J hJ).symm ▸ Subgroup.mem_inf.mpr ⟨ha, hJa⟩)
  obtain ⟨J₀, hJ₀⟩ := h.nonempty
  set Z := Subgroup.zpowers a with hZ
  set Y := K ⊓ Subgroup.centralizer {a} with hY
  have hbK : b ∈ Subgroup.normalizer (K : Set Γ) := h.normalizes hb
  have hperm : ∀ c ∈ A, ∀ J ∈ lcal K, J.map (MulAut.conj c).toMonoidHom ∈ lcal K :=
    fun c hc _ hJ => map_conj_mem_lcal hJ (h.normalizes hc)
  have hbJ : J₀.map (MulAut.conj b).toMonoidHom ∈ lcal K := hperm b hb J₀ hJ₀
  have hsame : Diag.SameBlock (lcal K) Y J₀ (J₀.map (MulAut.conj b).toMonoidHom) := by
    intro y hy
    have hyb : b * y * b⁻¹ = y := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
      calc b * y * b⁻¹ = (y * b) * b⁻¹ := by rw [this]
        _ = y := by group
    have := (Diag.conj_mem_sSup_diff_map_iff (S := lcal K) (c := b) (hperm b hb) (hperm b⁻¹
      (inv_mem hb)) (J := J₀) (y := y))
    rw [hyb] at this
    exact this.symm
  obtain ⟨g, hg, hgJ⟩ := Diag.mem_conjOrbit_of_sameBlock hp hK haK hap hJ₀ (haJ J₀ hJ₀)
    (le_refl Y) hbJ hsame
  have hgA : g ∈ A := Subgroup.zpowers_le.mpr ha hg
  have hnN : g⁻¹ * b ∈ Subgroup.normalizer (J₀ : Set Γ) := Diag.mem_normalizer_of_map_conj_eq hgJ
  have hnA : g⁻¹ * b ∈ A := mul_mem (inv_mem hgA) hb
  have hnY : ∀ y ∈ Y, (g⁻¹ * b) * y = y * (g⁻¹ * b) := by
    intro y hy
    have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have hyg : y * g = g * y := by
      have : y ∈ Subgroup.centralizer (Z : Set Γ) := by
        rw [hZ, centralizer_zpowers_eq]; exact (Subgroup.mem_inf.mp hy).2
      exact (Subgroup.mem_centralizer_iff.mp this g hg).symm
    have hyg' : y * g⁻¹ = g⁻¹ * y := by
      have h2 := congrArg (fun z => g⁻¹ * z * g⁻¹) hyg
      simpa [mul_assoc] using h2.symm
    calc g⁻¹ * b * y = g⁻¹ * (b * y) := by group
      _ = g⁻¹ * (y * b) := by rw [hyb]
      _ = (g⁻¹ * y) * b := by group
      _ = (y * g⁻¹) * b := by rw [hyg']
      _ = y * (g⁻¹ * b) := by group
  have hnC : g⁻¹ * b ∈ Subgroup.centralizer (J₀ : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxproj : x ∈ projIn (lcal K) J₀ Y := by
      rw [Diag.projIn_inf_centralizer_eq_self hp hK haK hap hJ₀ (haJ J₀ hJ₀)]; exact hx
    obtain ⟨-, l, hl, hxl⟩ := (mem_proj_iff (hK.commute_sSup_diff hJ₀)).mp hxproj
    set n := g⁻¹ * b with hn
    have hJn : J₀.map (MulAut.conj n).toMonoidHom = J₀ := L514.map_conj_eq_of_mem_normalizer hnN
    have hnxl := hnY _ hxl
    have hnl : n * l * n⁻¹ ∈ sSup (lcal K \ {J₀}) := by
      have := (Diag.conj_mem_sSup_diff_map_iff (S := lcal K) (c := n) (hperm n hnA)
        (hperm n⁻¹ (inv_mem hnA)) (J := J₀) (y := l)).mpr hl
      rwa [hJn] at this
    have hnx : n * x * n⁻¹ ∈ J₀ := (Subgroup.mem_normalizer_iff.mp hnN x).mp hx
    have hprod : (n * x * n⁻¹) * (n * l * n⁻¹) = x * l := by
      calc (n * x * n⁻¹) * (n * l * n⁻¹) = n * (x * l) * n⁻¹ := by group
        _ = (x * l) * n * n⁻¹ := by rw [hnxl]
        _ = x * l := by group
    have hmem : x⁻¹ * (n * x * n⁻¹) ∈ J₀ ⊓ sSup (lcal K \ {J₀}) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx) hnx, ?_⟩
      have h1 : x⁻¹ * (n * x * n⁻¹) = l * (n * l * n⁻¹)⁻¹ := by
        have h2 : x⁻¹ * ((n * x * n⁻¹) * (n * l * n⁻¹)) * (n * l * n⁻¹)⁻¹ =
            x⁻¹ * (n * x * n⁻¹) := by group
        rw [← h2, hprod]; group
      rw [h1]
      exact mul_mem hl (inv_mem hnl)
    rw [(hK.indep hJ₀).eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have : n * x = x * n := by
      have := congrArg (· * n) hmem.symm
      simpa [mul_assoc] using this
    exact this.symm
  have hnCK := mem_centralizer_of_centralizes_component h hJ₀ hnA hnC
  have hb' : b = g * (g⁻¹ * b) := by group
  rw [hb', sup_comm]
  exact mul_mem (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right ⟨hnA, hnCK⟩)

theorem le_wSub_or_le_cenIn_of_diagSetting {p : ℕ} (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (A K B : Subgroup Γ), DiagSetting p A K → CycStab A K → B ≤ A →
      Nat.card K = n → K ≤ wSub A B K ∨ K ≤ cenIn K (B : Set Γ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A K B h hcyc hB hn
  have hp := h.prime
  set C := A ⊓ Subgroup.centralizer (K : Set Γ) with hC
  have hCA : C ≤ A := inf_le_left
  have hCX : C ≤ Subgroup.centralizer (K : Set Γ) := inf_le_right
  by_cases hcycA : ∃ a' ∈ A, A ≤ C ⊔ Subgroup.zpowers a'
  · obtain ⟨a', ha', hAa'⟩ := hcycA
    exact le_wSub_or_le_cenIn_of_cyclic hp h.elemAbelian hCA hCX hB ha' hAa'
  · push Not at hcycA
    obtain ⟨J₀, hJ₀⟩ := h.nonempty
    set N := A ⊓ Subgroup.normalizer (J₀ : Set Γ) with hN0
    have hN : ∀ J ∈ lcal K, N = A ⊓ Subgroup.normalizer (J : Set Γ) := fun J hJ =>
      stabilizer_eq h hJ₀ hJ
    have hCN : C ≤ N := inf_le_inf_left _ (centralizer_le_normalizer_of_mem_lcal hJ₀)
    obtain ⟨n₀, hn₀A, hn₀⟩ := hcyc J₀ hJ₀
    obtain ⟨x, hxA, hxN⟩ : ∃ x ∈ A, x ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hcycA n₀ hn₀A (fun x hx => hn₀ (hcon x hx))
    obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ∉ C ⊔ Subgroup.zpowers x := by
      by_contra hcon
      push Not at hcon
      exact hcycA x hxA (fun y hy => hcon y hy)
    obtain ⟨a, haAN, hind⟩ :=
      exists_three_semiregular hp hp2 h.elemAbelian hCA hCN hxA hxN hyA hyx
    have hYd : ∀ i, DiagSetting p A (K ⊓ Subgroup.centralizer {a i}) ∧
        CycStab A (K ⊓ Subgroup.centralizer {a i}) := fun i => by
      obtain ⟨hd, -, hcy⟩ := diagSetting_centralizer h hN (haAN i).1 (haAN i).2
      exact ⟨hd, hcy hcyc⟩
    have hYlt : ∀ i, Nat.card ↥(K ⊓ Subgroup.centralizer {a i}) < n := by
      intro i
      rw [← hn]
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun heq => (haAN i).2 ?_)
      refine hCN (Subgroup.mem_inf.mpr ⟨(haAN i).1, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkc : k ∈ K ⊓ Subgroup.centralizer {a i} := heq.symm ▸ hk
      exact Subgroup.mem_centralizer_singleton_iff.mp hkc.2
    have hih : ∀ i, K ⊓ Subgroup.centralizer {a i} ≤ wSub A B K ∨
        K ⊓ Subgroup.centralizer {a i} ≤ cenIn K (B : Set Γ) := fun i => by
      rcases ih _ (hYlt i) A _ B (hYd i).1 (hYd i).2 hB rfl with h1 | h1
      · exact Or.inl (h1.trans (wSub_mono A B inf_le_left))
      · exact Or.inr (h1.trans (cenIn_mono_left inf_le_left _))
    have hAN : ∀ L : Subgroup Γ, Admits A L → A ≤ Subgroup.normalizer (L : Set Γ) := fun L hL => hL
    have key : ∀ (L : Subgroup Γ) (i j : Fin 3), i ≠ j → L ≤ K →
        A ≤ Subgroup.normalizer (L : Set Γ) → K ⊓ Subgroup.centralizer {a i} ≤ L →
        K ⊓ Subgroup.centralizer {a j} ≤ L → K ≤ L := by
      intro L i j hij hLK hAL hi hj
      rcases DiagSetting.eq_or_eq_top h hN (haAN i).1 (haAN i).2 hLK hi hAL with hL | hL
      · exfalso
        have hle : K ⊓ Subgroup.centralizer {a j} ≤ Subgroup.centralizer {a i} :=
          (hj.trans hL.le).trans inf_le_right
        have := mem_sup_of_centralizer_le h hN (haAN j).1 (haAN i).1 (haAN j).2 hle
        exact hind j i hij.symm this
      · exact hL ▸ le_rfl
    classical
    let f : Fin 3 → Bool := fun i => decide (K ⊓ Subgroup.centralizer {a i} ≤ wSub A B K)
    obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    by_cases hW : K ⊓ Subgroup.centralizer {a i} ≤ wSub A B K
    · have hWj : K ⊓ Subgroup.centralizer {a j} ≤ wSub A B K := by
        have : f j = true := by rw [← hfij]; simp [f, hW]
        simpa [f] using this
      exact Or.inl (key _ i j hij (wSub_le A B K) (admits_wSub h.elemAbelian.1 h.normalizes)
        hW hWj)
    · have hWj : ¬ K ⊓ Subgroup.centralizer {a j} ≤ wSub A B K := by
        intro hj
        have : f i = true := by rw [hfij]; simp [f, hj]
        exact hW (by simpa [f] using this)
      have hZi := (hih i).resolve_left hW
      have hZj := (hih j).resolve_left hWj
      exact Or.inr (key _ i j hij (cenIn_le_left K _)
        (admits_cenIn h.elemAbelian.1 h.normalizes hB) hZi hZj)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
