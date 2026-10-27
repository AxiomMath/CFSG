module

public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftRot

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggCross_mul_mul_eq_rot {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]
    (h2 : (2 : F) = 0) (hn : 3 ≤ n) {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hc₂ : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hc₃ : φ₁.comp (slLowerBlockHom n F) = φ₃.comp (slUpperBlockHom n F))
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hfar' : Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F j)) (φ₂ (weylRep n F i))) :
    φ₂ (weylRep n F j) * φ₃ (weylRep n F j) * φ₂ (weylRep n F j) =
      ggRotLift h2 φ₂ φ₃ (weylRep n F j) := by
  have h0n : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hjn : n - 1 < n := Nat.sub_lt h0n (by norm_num)
  obtain rfl : i = ⟨0, h0n⟩ := Fin.ext (by simpa using hi)
  obtain rfl : j = ⟨n - 1, hjn⟩ := Fin.ext (by
    show j.val = n - 1
    omega)
  let i0 : Fin n := ⟨0, h0n⟩
  let jn : Fin n := ⟨n - 1, hjn⟩
  let g : X := φ₂ (slPerm h2 (finRotate (n + 1)))
  let b : X := φ₂ (weylRep n F jn)
  let b₃ : X := φ₃ (weylRep n F jn)
  let b' : X := ggRotLift h2 φ₂ φ₃ (weylRep n F jn)
  change b * b₃ * b = b'
  have hfar : Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F jn))
      (φ₂ (weylRep n F i0)) := hfar'
  have hc : φ₂.comp (slLowerBlockHom n F) =
      (ggRotLift h2 φ₂ φ₃).comp (slUpperBlockHom n F) :=
    ggRotLift_compat h2 hc₂ hc₃
  have hcomm (s : SpecialLinearGroup (Fin n) F) :
      Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F jn))
        (φ₂ (slUpperBlockHom n F s)) :=
    commute_slUpperBlockHom_of_transvection (by omega)
      (fun a b hab ha hb c => slCompat_commute h2 hn hc hfar hab ha hb c) s
  have hjncs : jn.castSucc.val = n - 1 := rfl
  have hsucc : jn.succ = Fin.last n := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_last]
    change n - 1 + 1 = n
    omega
  have hlast_ne : jn.castSucc ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_last] at hv
    omega
  have hfix : (finRotate (n + 1) * Equiv.swap jn.castSucc jn.succ) (Fin.last n) =
      Fin.last n := by
    have hswap : Equiv.swap jn.castSucc jn.succ (Fin.last n) = jn.castSucc := by
      rw [← hsucc, Equiv.swap_apply_right]
    rw [Equiv.Perm.mul_apply, hswap]
    apply Fin.ext
    rw [coe_finRotate_of_ne_last hlast_ne, Fin.val_last]
    omega
  obtain ⟨s, hs⟩ := exists_slUpperBlockHom_eq_slPerm h2 hfix
  have hm : g * b = φ₂ (slUpperBlockHom n F s) := by
    change φ₂ (slPerm h2 (finRotate (n + 1))) * φ₂ (weylRep n F jn) =
      φ₂ (slUpperBlockHom n F s)
    rw [← map_mul, ← slPerm_swap_castSucc_succ h2 jn, ← map_mul, hs]
  have hb2 : b * b = 1 := by
    change φ₂ (weylRep n F jn) * φ₂ (weylRep n F jn) = 1
    rw [← map_mul, weylRep_mul_self n h2, map_one]
  have hcomm' : Commute b' (g * b) := by
    change Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F jn)) (g * b)
    rw [hm]
    exact hcomm s
  have hb'g : b' = g * b₃ * g⁻¹ := by
    change ggRotLift h2 φ₂ φ₃ (weylRep n F jn) = g * b₃ * g⁻¹
    rw [ggRotLift_apply]
  have hmX : (g * b) * (b * b₃ * b) * (g * b)⁻¹ = g * b₃ * g⁻¹ := by
    calc (g * b) * (b * b₃ * b) * (g * b)⁻¹
        = g * (b * b) * b₃ * (b * b⁻¹) * g⁻¹ := by group
      _ = g * b₃ * g⁻¹ := by rw [hb2]; group
  have hb'X : b' = (g * b) * (b * b₃ * b) * (g * b)⁻¹ := by
    rw [hb'g, hmX]
  have hmconj : (g * b)⁻¹ * b' * (g * b) = b' := by
    calc (g * b)⁻¹ * b' * (g * b)
        = (g * b)⁻¹ * (b' * (g * b)) := by group
      _ = (g * b)⁻¹ * ((g * b) * b') := by rw [hcomm']
      _ = b' := by group
  calc b * b₃ * b = (g * b)⁻¹ * b' * (g * b) := by
        rw [hb'X]; group
    _ = b' := hmconj

theorem ggCross_of_far {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F] (h2 : (2 : F) = 0)
    (hn : 3 ≤ n) {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hc₂ : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hc₃ : φ₁.comp (slLowerBlockHom n F) = φ₃.comp (slUpperBlockHom n F))
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hfar₂ : Commute (φ₂ (weylRep n F j)) (φ₁ (weylRep n F i)))
    (hfar₃ : Commute (φ₃ (weylRep n F j)) (φ₁ (weylRep n F i)))
    (hfar' : Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F j)) (φ₂ (weylRep n F i))) :
    (φ₃ (weylRep n F j) * φ₂ (weylRep n F j)) ^ 3 = 1 ∧
      ∀ g, φ₂ (weylRep n F j) * φ₃ (weylRep n F j) * φ₂ (weylRep n F j) * φ₁ g =
        φ₁ g * (φ₂ (weylRep n F j) * φ₃ (weylRep n F j) * φ₂ (weylRep n F j)) := by
  have hX := ggCross_mul_mul_eq_rot h2 hn hc₂ hc₃ hi hj hfar'
  have h0n : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hjn : n - 1 < n := Nat.sub_lt h0n (by norm_num)
  obtain rfl : i = ⟨0, h0n⟩ := Fin.ext (by simpa using hi)
  obtain rfl : j = ⟨n - 1, hjn⟩ := Fin.ext (by
    show j.val = n - 1
    omega)
  let i0 : Fin n := ⟨0, h0n⟩
  let jn : Fin n := ⟨n - 1, hjn⟩
  let b : X := φ₂ (weylRep n F jn)
  let b₃ : X := φ₃ (weylRep n F jn)
  let b' : X := ggRotLift h2 φ₂ φ₃ (weylRep n F jn)
  have hX' : b * b₃ * b = b' := hX
  have hfar₂' : Commute b (φ₁ (weylRep n F i0)) := hfar₂
  have hfar₃' : Commute b₃ (φ₁ (weylRep n F i0)) := hfar₃
  have hc : φ₂.comp (slLowerBlockHom n F) =
      (ggRotLift h2 φ₂ φ₃).comp (slUpperBlockHom n F) :=
    ggRotLift_compat h2 hc₂ hc₃
  have hfar : Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F jn))
      (φ₂ (weylRep n F i0)) := hfar'
  have hcomm (s : SpecialLinearGroup (Fin n) F) :
      Commute (ggRotLift h2 φ₂ φ₃ (weylRep n F jn))
        (φ₂ (slUpperBlockHom n F s)) :=
    commute_slUpperBlockHom_of_transvection (by omega)
      (fun a b hab ha hb c => slCompat_commute h2 hn hc hfar hab ha hb c) s
  have hb2 : b * b = 1 := by
    change φ₂ (weylRep n F jn) * φ₂ (weylRep n F jn) = 1
    rw [← map_mul, weylRep_mul_self n h2, map_one]
  have hb3b : b₃ * b = b * b' := by
    calc b₃ * b = (b * b) * b₃ * b := by rw [hb2, one_mul]
      _ = b * (b * b₃ * b) := by group
      _ = b * b' := by rw [hX']
  have hbψ : b = ggRotLift h2 φ₂ φ₃ (weylRep n F ⟨n - 2, by omega⟩) := by
    change φ₂ (weylRep n F jn) =
      ggRotLift h2 φ₂ φ₃ (weylRep n F ⟨n - 2, by omega⟩)
    exact slCompat_weylRep (n := n) (by omega) (ggRotLift_compat h2 hc₂ hc₃)
  have hksv : (⟨n - 2, by omega⟩ : Fin n).castSucc.val = n - 2 := rfl
  have hjncs : jn.castSucc.val = n - 1 := rfl
  have hsucc : (⟨n - 2, by omega⟩ : Fin n).succ = jn.castSucc := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_castSucc]
    change n - 2 + 1 = n - 1
    omega
  have hjnsv : jn.succ.val = n := by
    rw [Fin.val_succ]
    change n - 1 + 1 = n
    omega
  have h3cyc : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n).castSucc
      (⟨n - 2, by omega⟩ : Fin n).succ * Equiv.swap jn.castSucc jn.succ).IsThreeCycle := by
    rw [hsucc, Equiv.swap_comm (⟨n - 2, by omega⟩ : Fin n).castSucc jn.castSucc]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (by intro h; have hv := congrArg Fin.val h; omega)
      (by intro h; have hv := congrArg Fin.val h; omega)
      (by intro h; have hv := congrArg Fin.val h; omega)
  have hcube3 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n).castSucc
      (⟨n - 2, by omega⟩ : Fin n).succ * Equiv.swap jn.castSucc jn.succ) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, h3cyc.orderOf]
  have hcube : (b₃ * b) ^ 3 = 1 := by
    rw [hb3b, hbψ]
    change (ggRotLift h2 φ₂ φ₃ (weylRep n F ⟨n - 2, by omega⟩) *
      ggRotLift h2 φ₂ φ₃ (weylRep n F jn)) ^ 3 = 1
    rw [← map_mul, ← map_pow,
      ← slPerm_swap_castSucc_succ h2 (⟨n - 2, by omega⟩ : Fin n),
      ← slPerm_swap_castSucc_succ h2 jn, ← map_mul, ← map_pow, hcube3, map_one, map_one]
  refine ⟨hcube, ?_⟩
  intro x
  let H : Subgroup (SpecialLinearGroup (Fin (n + 1)) F) :=
    (Subgroup.centralizer ({b'} : Set X)).comap φ₁
  have hlow : ∀ s, slLowerBlockHom n F s ∈ H := by
    intro s
    change φ₁ (slLowerBlockHom n F s) ∈ Subgroup.centralizer ({b'} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hφ : φ₁ (slLowerBlockHom n F s) = φ₂ (slUpperBlockHom n F s) :=
      DFunLike.congr_fun hc₂ s
    rw [hφ]
    exact (hcomm s).symm
  have hmem : weylRep n F i0 ∈ H := by
    change φ₁ (weylRep n F i0) ∈ Subgroup.centralizer ({b'} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hX']
    exact (hfar₂'.symm.mul_right hfar₃'.symm).mul_right hfar₂'.symm
  have htop : H = ⊤ :=
    eq_top_of_slLowerBlockHom_le h2 (by omega) H hlow (i := i0) rfl hmem
  have hxH : x ∈ H := by rw [htop]; exact Subgroup.mem_top _
  change φ₁ x ∈ Subgroup.centralizer ({b'} : Set X) at hxH
  rw [Subgroup.mem_centralizer_singleton_iff] at hxH
  rw [hX']
  exact hxH.symm

end CFSG.StandardType
