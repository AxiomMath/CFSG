module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzDefs
public import CFSG.Quasithin.Vol2.Ch12Sec7GzInputs
public import CFSG.Quasithin.Vol2.Ch12Sec7GzConj

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 S127.I77

theorem gzNotLeM_of (h71 : Setup1271) (h74 : Lemma12_7_4) (h125 : Lemma12_7_5)
    (hK : KtLine1277) (hM : MLine1277) (hMV : MEqNormV1277) : GzNotLeM1277 := by
  intro G _ _ T L V h t ht h18 hGt z hzV hz45
  have s : Set77 G T L V t := set77_of h71 h74 h125 h ht h18 hGt
  have hNLV : Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) :=
    hMV G T L V t s
  have hne1 : ∀ v : G, (Subgroup.centralizer ({v} : Set G)).relIndex L = 45 → v ≠ 1 := by
    intro v hv hv1
    subst hv1
    have htop : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop, Subgroup.relIndex_top_left] at hv
    norm_num at hv
  obtain ⟨z₁, -, -, -, t₁, -, -, -, ht₁18, horb⟩ := (h74 G T L V h).1
  have hVtV : Vt L t ≤ V := s.d.vt_le
  obtain ⟨U, -, hUab, hU64, hUV, hUD, hUN, k, hk0, hkK, hkint⟩ := hK G T L V t s
  have hUL : U ≤ Subgroup.normalizer (L : Set G) := by
    rw [hNLV]
    exact hUN
  have hVtU : Vt L t ≤ U := by
    intro x hx
    have h1 : x ∈ V.map (MulAut.conj (k 0)).toMonoidHom ⊓
        V.map (MulAut.conj (k 1)).toMonoidHom ⊓ U := by
      rw [hkint 0 1 (by decide)]
      exact hx
    exact (Subgroup.mem_inf.mp h1).2
  obtain ⟨hM1, ⟨g, hgN, hgt, hgt'⟩, z₀, hz₀D, hz₀45, hz₀9⟩ :=
    hM G T L V t s U hUab hU64 hUL hUV hUD (le_inf hVtU hVtV)
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_inf.mp hgN).1
  have hgD : g ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hgN).2
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := by
    rw [← hNLV]
    exact hgL
  have hStep1 : ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) →
      x ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) →
        x ∈ Subgroup.normalizer (U : Set G) := by
    intro x hxL hxD
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := by
      rw [← hNLV]
      exact hxL
    have hxD' : x⁻¹ ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hxD
    have hxV' : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hxV
    have hsub : cjS x U ≤ Subgroup.normalizer (L : Set G) ⊓
        Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := by
      intro y hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hy' : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
        rw [hy']
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxL (hUL (mem_cjS_iff.mp hy)))
          (Subgroup.inv_mem _ hxL)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : d ∈ U ⊓ V := hd
      have hd2 : x⁻¹ * d * x ∈ U ⊓ V := by
        have h3 := (Subgroup.mem_normalizer_iff.mp hxD' d).mp hd'
        rwa [inv_inv] at h3
      have hu : x⁻¹ * y * x ∈ U := mem_cjS_iff.mp hy
      have hc : (x⁻¹ * y * x) * (x⁻¹ * d * x) = (x⁻¹ * d * x) * (x⁻¹ * y * x) :=
        congrArg Subtype.val
          (hUab.1.is_comm.comm ⟨x⁻¹ * y * x, hu⟩ ⟨x⁻¹ * d * x, (Subgroup.mem_inf.mp hd2).1⟩)
      calc d * y = x * ((x⁻¹ * d * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * y * x) * (x⁻¹ * d * x)) * x⁻¹ := by rw [hc]
        _ = y * d := by group
    rcases hM1 (cjS x U) hsub (isElemAbelian_cjS hUab) (by rw [card_cjS, hU64]) with h | h
    · exfalso
      apply hUV
      calc U = cjS x⁻¹ (cjS x U) := by rw [← cjS_mul, inv_mul_cancel, cjS_one]
        _ = cjS x⁻¹ V := by rw [h]
        _ = V := cjS_eq_of_mem_normalizer hxV'
    · exact mem_normalizer_of_cjS_eq h
  have hgU : g ∈ Subgroup.normalizer (U : Set G) := hStep1 g hgL hgD
  have hPinj : ∀ i j : Fin 5, cjS (k i) V = cjS (k j) V → i = j := by
    intro i j hij
    by_contra hne
    have hI : cjS (k i) V ⊓ cjS (k j) V ⊓ U = Vt L t := hkint i j hne
    rw [← hij, inf_idem] at hI
    have e : cjS (k i) (U ⊓ V) = cjS (k i) V ⊓ U := by
      rw [cjS_inf, cjS_eq_of_mem_normalizer (Subgroup.mem_inf.mp (hkK i)).2, inf_comm]
    have h16 : Nat.card ↥(cjS (k i) V ⊓ U) = 16 := by
      rw [← e, card_cjS, hUD]
    rw [hI, s.d.card_Vt] at h16
    norm_num at h16
  have hQinj : ∀ j j' : Fin 4, cjS (g * k j.succ) V = cjS (g * k j'.succ) V → j = j' := by
    intro j j' hjj
    have h2 := congrArg (cjS g⁻¹) hjj
    rw [← cjS_mul, ← cjS_mul, inv_mul_cancel_left, inv_mul_cancel_left] at h2
    exact Fin.succ_injective _ (hPinj _ _ h2)
  have hPQ : ∀ (i : Fin 5) (j : Fin 4), cjS (k i) V ≠ cjS (g * k j.succ) V := by
    intro i j hij
    have hkC : t * k j.succ = k j.succ * t :=
      Subgroup.mem_centralizer_iff.mp
        (s.le_centralizer_vt (Subgroup.mem_inf.mp (hkK j.succ)).1) t s.d.mem_vt
    have hmem : g * t * g⁻¹ ∈ cjS (g * k j.succ) V := by
      rw [mem_cjS_iff]
      have e : (g * k j.succ)⁻¹ * (g * t * g⁻¹) * (g * k j.succ) = t := by
        calc (g * k j.succ)⁻¹ * (g * t * g⁻¹) * (g * k j.succ)
            = (k j.succ)⁻¹ * t * k j.succ := by group
          _ = (k j.succ)⁻¹ * (t * k j.succ) := by group
          _ = (k j.succ)⁻¹ * (k j.succ * t) := by rw [hkC]
          _ = t := by group
      rw [e]
      exact s.d.mem
    rw [← hij] at hmem
    by_cases hi : i = 0
    · subst hi
      have hV : cjS (g * k j.succ) V = V := by
        rw [← hij, hk0, cjS_one]
      have hnV : g * k j.succ ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_cjS_eq hV
      have hkV : k j.succ ∈ Subgroup.normalizer (V : Set G) := by
        have h3 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hgV) hnV
        rwa [inv_mul_cancel_left] at h3
      have h0 : cjS (k j.succ) V = cjS (k 0) V := by
        rw [cjS_eq_of_mem_normalizer hkV, hk0, cjS_one]
      exact Fin.succ_ne_zero j (hPinj _ _ h0)
    · have hI : cjS (k 0) V ⊓ cjS (k i) V ⊓ U = Vt L t := hkint 0 i (Ne.symm hi)
      rw [hk0, cjS_one] at hI
      have hmem' : g * t * g⁻¹ ∈ V ⊓ cjS (k i) V ⊓ U :=
        ⟨⟨(Subgroup.mem_inf.mp hgt).2, hmem⟩, (Subgroup.mem_inf.mp hgt).1⟩
      rw [hI] at hmem'
      exact hgt' hmem'
  have hfH : ∀ x : Fin 5 ⊕ Fin 4,
      Sum.elim k (fun j : Fin 4 => g * k j.succ) x ∈ Subgroup.normalizer (U : Set G) := by
    intro x
    rcases x with i | j
    · exact (Subgroup.mem_inf.mp (hkK i)).2
    · exact Subgroup.mul_mem _ hgU (Subgroup.mem_inf.mp (hkK j.succ)).2
  have hinj : Function.Injective
      (fun x : Fin 5 ⊕ Fin 4 => cjS (Sum.elim k (fun j : Fin 4 => g * k j.succ) x) V) := by
    rintro (i | j) (i' | j') hxy
    · have h1 : cjS (k i) V = cjS (k i') V := hxy
      rw [hPinj i i' h1]
    · exact absurd (show cjS (k i) V = cjS (g * k j'.succ) V from hxy) (hPQ i j')
    · exact absurd (show cjS (k i') V = cjS (g * k j.succ) V from hxy.symm) (hPQ i' j)
    · have h1 : cjS (g * k j.succ) V = cjS (g * k j'.succ) V := hxy
      rw [hQinj j j' h1]
  have hcard9 : Nat.card (Fin 5 ⊕ Fin 4) = 9 := by simp
  have hB9 : 9 ≤ (Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer (V : Set G)).relIndex (Subgroup.normalizer (U : Set G)) := by
    have h := le_relIndex_of_cjS (H := Subgroup.normalizer (U : Set G)) (V := V)
      (Sum.elim k (fun j : Fin 4 => g * k j.succ)) hfH hinj
    rw [hcard9] at h
    exact h
  have hz₀V : z₀ ∈ V := (Subgroup.mem_inf.mp hz₀D).2
  have hz₀U : z₀ ∈ U := (Subgroup.mem_inf.mp hz₀D).1
  have hz₀1 : z₀ ≠ 1 := hne1 z₀ hz₀45
  have hsubB : Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) ≤
        Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G) := by
    intro x hx
    obtain ⟨hxL, hxD⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hStep1 x hxL hxD, ?_⟩
    rw [← hNLV]
    exact hxL
  have hmono : (Subgroup.centralizer ({z₀} : Set G)).relIndex
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ≤
      (Subgroup.centralizer ({z₀} : Set G)).relIndex
        (Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G)) :=
    Subgroup.relIndex_le_of_le_right hsubB (relIndex_ne_zero_of_finite _ _)
  have hz₀9' : 9 ≤ (Subgroup.centralizer ({z₀} : Set G)).relIndex
      (Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G)) :=
    le_trans hz₀9 hmono
  have hz₀not : ¬ Subgroup.centralizer ({z₀} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro hC
    have hle : Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({z₀} : Set G) ≤
        Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G) := by
      intro x hx
      obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxU, ?_⟩
      rw [← hNLV]
      exact hC hxC
    have hprod := relIndex_mul_relIndex_lt (H := Subgroup.normalizer (U : Set G))
      (B := Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G))
      inf_le_left hz₀U hz₀1 le_rfl hle
    rw [hU64] at hprod
    have h81 : 9 * 9 ≤
        (Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
          (Subgroup.normalizer (U : Set G)) *
        (Subgroup.centralizer ({z₀} : Set G)).relIndex
          (Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G)) :=
      Nat.mul_le_mul hB9 hz₀9'
    have h64 := lt_of_le_of_lt h81 hprod
    norm_num at h64
  have horbit : ∀ v ∈ V, v ≠ 1 → (Subgroup.centralizer ({v} : Set G)).relIndex L = 45 →
      ∃ l ∈ L, l * v * l⁻¹ = z₁ := by
    intro v hv hv1 hv45
    rcases horb v hv hv1 with ⟨l, hl, hlv⟩ | ⟨l, hl, hlv⟩
    · exact ⟨l, hl, hlv⟩
    · exfalso
      have hc := relIndex_centralizer_conj (x := v) hl
      rw [hlv, ht₁18, hv45] at hc
      norm_num at hc
  obtain ⟨l₀, hl₀, hl₀z⟩ := horbit z₀ hz₀V hz₀1 hz₀45
  obtain ⟨l₁, hl₁, hl₁z⟩ := horbit z hzV (hne1 z hz45) hz45
  obtain ⟨m, hmL, hzm⟩ : ∃ m ∈ L, z = m * z₀ * m⁻¹ := by
    refine ⟨l₁⁻¹ * l₀, L.mul_mem (L.inv_mem hl₁) hl₀, ?_⟩
    rw [show l₁⁻¹ * l₀ * z₀ * (l₁⁻¹ * l₀)⁻¹ = l₁⁻¹ * (l₀ * z₀ * l₀⁻¹) * l₁ by group, hl₀z,
      ← hl₁z]
    group
  intro hCz
  apply hz₀not
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hw : m * y * m⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hzm]
    calc m * y * m⁻¹ * (m * z₀ * m⁻¹) = m * (y * z₀) * m⁻¹ := by group
      _ = m * (z₀ * y) * m⁻¹ := by rw [hy]
      _ = m * z₀ * m⁻¹ * (m * y * m⁻¹) := by group
  have hwN : m * y * m⁻¹ ∈ Subgroup.normalizer (L : Set G) := hCz hw
  have hmN : m ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hmL
  have e : m⁻¹ * (m * y * m⁻¹) * m = y := by group
  rw [← e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) hwN) hmN

end CFSG.Quasithin.H13.I1277
