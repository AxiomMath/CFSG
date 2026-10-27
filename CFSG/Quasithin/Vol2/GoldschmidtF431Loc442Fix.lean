module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsOrd

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.Loc442

universe u v

section Basic

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] {M2 : Subgroup Mb} {t : Mb}
  {b2 : M2 →* M}

@[expose] def locX (M2 : Subgroup Mb) (b2 : M2 →* M) (t : Mb) (ht : t ∈ M2) : Subgroup M :=
  (Subgroup.centralizer ({(⟨t, ht⟩ : M2)} : Set M2)).map b2

theorem mem_locX {ht : t ∈ M2} {y : M} :
    y ∈ locX M2 b2 t ht ↔ ∃ x : M2, (x : Mb) * t = t * (x : Mb) ∧ b2 x = y := by
  unfold locX
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hx), rfl⟩

end Basic

section Fix

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {z t q : Mb} {Vb : Subgroup Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem locX_comm_t (D : Loc442Datum M1 M2 T z t Vb q) (C : F431Comp M1 M2 b1 b2) {y : M}
    (hy : y ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)) :
    y * amalgamMap b1 b2 t = amalgamMap b1 b2 t * y := by
  obtain ⟨x, hx, rfl⟩ := mem_locX.1 hy
  rw [amalgamMap_of_mem₂ b1 b2 C.agree (D.lie.T_le₂ D.lie.t_mem), ← map_mul, ← map_mul]
  exact congrArg b2 (Subtype.ext hx)

theorem locX_of_cent_z (D : Loc442Datum M1 M2 T z t Vb q) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) {k : M}
    (hkz : k * amalgamMap b1 b2 z = amalgamMap b1 b2 z * k)
    (hkt : k * amalgamMap b1 b2 t = amalgamMap b1 b2 t * k) :
    k ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) := by
  obtain ⟨y, rfl⟩ := hb (Subgroup.mem_centralizer_singleton_iff.2 hkz)
  have htM1 : t ∈ M1 := D.lie.T_le₁ D.lie.t_mem
  rw [amalgamMap_of_mem₁ b1 b2 htM1, ← map_mul, ← map_mul] at hkt
  have hy : (y : Mb) * t = t * (y : Mb) := congrArg Subtype.val (C.inj₁ hkt)
  have hyM2 : (y : Mb) ∈ M2 := D.lie.cent_t (Subgroup.mem_centralizer_singleton_iff.2 hy)
  exact mem_locX.2 ⟨⟨y, hyM2⟩, hy, (C.agree y y.2 hyM2).symm⟩

end Fix

section Fusion

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {z t q : Mb} {Vb : Subgroup Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem locX_fusion (D : Loc442Datum M1 M2 T z t Vb q) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {g : M}
    (hg : g * amalgamMap b1 b2 t = amalgamMap b1 b2 t * g)
    (hu : g⁻¹ * amalgamMap b1 b2 z * g ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)) :
    ∃ m ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem),
      g⁻¹ * amalgamMap b1 b2 z * g = m⁻¹ * amalgamMap b1 b2 z * m := by
  have hzM2 : z ∈ M2 := D.lie.T_le₂ D.lie.z_mem
  have htM1 : t ∈ M1 := D.lie.T_le₁ D.lie.t_mem
  have htM2 : t ∈ M2 := D.lie.T_le₂ D.lie.t_mem
  obtain ⟨ub, hub, hbu⟩ := mem_locX.1 hu
  have hψub : amalgamMap b1 b2 (ub : Mb) = g⁻¹ * amalgamMap b1 b2 z * g := by
    rw [amalgamMap_of_mem₂ b1 b2 C.agree ub.2]
    exact hbu
  have hconj : IsConj (amalgamMap b1 b2 z) (g⁻¹ * amalgamMap b1 b2 z * g) :=
    isConj_iff.2 ⟨g⁻¹, by simp⟩
  have hord : orderOf (ub : Mb) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective b2 C.inj₂ ub, hbu,
      ← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hconj]
    exact D.lie.orderOf_amalgamMap₁ C
  have hSyl2 : IsSylowTwoOf T M2 := F7.isSylowTwoOf_mono_right D.lie.sylow D.lie.T_le₂ le_top
  have hZ : IsConj z (ub : Mb) := by
    refine (D.lie.fusion_in C hnc hSyl2
      (fun a ha b hb' => amalgamMap_mul₂ b1 b2 C.agree ha hb') D.lie.z_mem D.lie.hz ub.2
      hord).2 ?_
    rw [hψub]
    exact hconj
  have hcent : (ub : Mb) ∈ Subgroup.centralizer ({t} : Set Mb) :=
    Subgroup.mem_centralizer_singleton_iff.2 hub
  rcases D.fusion _ hcent hZ with hV | ⟨n, hn, a, ha, b, hbT, hua, htb, b', hb'T, hch, hb'ne⟩
  · have hne1 : (ub : Mb) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      exact absurd hord (by norm_num)
    obtain ⟨x, hx, hxz⟩ := D.V_conj _ hV hne1
    have hxM2 : x ∈ M2 := D.lie.cent_t hx
    have hcX : b2 ⟨x, hxM2⟩ ∈ locX M2 b2 t htM2 :=
      mem_locX.2 ⟨⟨x, hxM2⟩, Subgroup.mem_centralizer_singleton_iff.1 hx, rfl⟩
    refine ⟨(b2 ⟨x, hxM2⟩)⁻¹, (locX M2 b2 t htM2).inv_mem hcX, ?_⟩
    rw [← hψub, hxz, psi_conj₂ C hxM2 hzM2, amalgamMap_of_mem₂ b1 b2 C.agree hxM2, inv_inv]
  · exfalso
    have haM2 : a ∈ M2 := D.lie.T_le₂ ha
    have hbM2 : b ∈ M2 := D.lie.T_le₂ hbT
    have hb'M1 : b' ∈ M1 := D.lie.T_le₁ hb'T
    obtain ⟨Y, hYz, hYb⟩ := chain_conj D.lie.T_le₁ D.lie.T_le₂ C hch
    have hYz : amalgamMap b1 b2 z = Y * amalgamMap b1 b2 a * Y⁻¹ := hYz
    have hYb : amalgamMap b1 b2 b' = Y * amalgamMap b1 b2 b * Y⁻¹ := hYb
    have hNa : amalgamMap b1 b2 (ub : Mb) =
        amalgamMap b1 b2 n * amalgamMap b1 b2 a * (amalgamMap b1 b2 n)⁻¹ := by
      rw [hua]
      exact psi_conj₂ C hn haM2
    have hNt : amalgamMap b1 b2 t =
        amalgamMap b1 b2 n * amalgamMap b1 b2 b * (amalgamMap b1 b2 n)⁻¹ := by
      conv_lhs => rw [htb]
      exact psi_conj₂ C hn hbM2
    have hB'1 : amalgamMap b1 b2 b' = b1 ⟨b', hb'M1⟩ := amalgamMap_of_mem₁ b1 b2 hb'M1
    have hTt1 : amalgamMap b1 b2 t = b1 ⟨t, htM1⟩ := amalgamMap_of_mem₁ b1 b2 htM1
    set P := amalgamMap b1 b2 z with hP
    set Tt := amalgamMap b1 b2 t with hTt
    set N := amalgamMap b1 b2 n with hN
    set A := amalgamMap b1 b2 a with hA
    set B := amalgamMap b1 b2 b with hB
    set B' := amalgamMap b1 b2 b' with hB'
    have hA' : A = N⁻¹ * (g⁻¹ * P * g) * N := by
      rw [← hψub, hNa]
      group
    have hB'' : B = N⁻¹ * Tt * N := by
      rw [hNt]
      group
    have hwP : g * N * Y⁻¹ * P = P * (g * N * Y⁻¹) := by
      calc g * N * Y⁻¹ * P = g * N * Y⁻¹ * (Y * (N⁻¹ * (g⁻¹ * P * g) * N) * Y⁻¹) := by
            rw [← hA', ← hYz]
        _ = P * (g * N * Y⁻¹) := by group
    obtain ⟨y, hy⟩ := hb (Subgroup.mem_centralizer_singleton_iff.2 hwP)
    have hgT : g⁻¹ * Tt * g = Tt := by
      calc g⁻¹ * Tt * g = g⁻¹ * (Tt * g) := by group
        _ = g⁻¹ * (g * Tt) := by rw [hg]
        _ = Tt := by group
    have hB'w : B' = (g * N * Y⁻¹)⁻¹ * Tt * (g * N * Y⁻¹) := by
      calc B' = Y * B * Y⁻¹ := hYb
        _ = Y * (N⁻¹ * Tt * N) * Y⁻¹ := by rw [hB'']
        _ = Y * (N⁻¹ * (g⁻¹ * Tt * g) * N) * Y⁻¹ := by rw [hgT]
        _ = (g * N * Y⁻¹)⁻¹ * Tt * (g * N * Y⁻¹) := by group
    have hbb : b1 ⟨b', hb'M1⟩ = b1 (y⁻¹ * ⟨t, htM1⟩ * y) := by
      rw [← hB'1, hB'w, map_mul, map_mul, map_inv, hy, hTt1]
    have hb'eq : b' = (y : Mb)⁻¹ * t * y := congrArg Subtype.val (C.inj₁ hbb)
    exact hb'ne ((y : Mb)⁻¹) (M1.inv_mem y.2) (by rw [hb'eq]; group)

end Fusion

section Fixed

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {z t q : Mb} {Vb : Subgroup Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem locX_fix_z (D : Loc442Datum M1 M2 T z t Vb q) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {g : M}
    (hg : g * amalgamMap b1 b2 t = amalgamMap b1 b2 t * g)
    (hu : g⁻¹ * amalgamMap b1 b2 z * g ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)) :
    g ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) := by
  obtain ⟨m, hm, hgm⟩ := locX_fusion D C hb hnc hg hu
  have hmi := locX_comm_t D C ((locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)).inv_mem hm)
  have hk : g * m⁻¹ ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) := by
    refine locX_of_cent_z D C hb ?_ ?_
    · calc g * m⁻¹ * amalgamMap b1 b2 z
          = g * (m⁻¹ * amalgamMap b1 b2 z * m) * m⁻¹ := by group
        _ = g * (g⁻¹ * amalgamMap b1 b2 z * g) * m⁻¹ := by rw [hgm]
        _ = amalgamMap b1 b2 z * (g * m⁻¹) := by group
    · calc g * m⁻¹ * amalgamMap b1 b2 t = g * (m⁻¹ * amalgamMap b1 b2 t) := mul_assoc _ _ _
        _ = g * (amalgamMap b1 b2 t * m⁻¹) := by rw [hmi]
        _ = g * amalgamMap b1 b2 t * m⁻¹ := (mul_assoc _ _ _).symm
        _ = amalgamMap b1 b2 t * g * m⁻¹ := by rw [hg]
        _ = amalgamMap b1 b2 t * (g * m⁻¹) := mul_assoc _ _ _
  have := (locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)).mul_mem hk hm
  simpa using this

theorem locX_fix_V (D : Loc442Datum M1 M2 T z t Vb q) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {v : M}
    (hv : ∃ vb : M2, (vb : Mb) ∈ Vb ∧ b2 vb = v) (hv1 : v ≠ 1) {g : M}
    (hg : g * amalgamMap b1 b2 t = amalgamMap b1 b2 t * g)
    (hu : g⁻¹ * v * g ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)) :
    g ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) := by
  obtain ⟨vb, hvb, rfl⟩ := hv
  have hne1 : (vb : Mb) ≠ 1 := fun h => hv1 (by rw [show vb = 1 from Subtype.ext h, map_one])
  obtain ⟨x, hx, hxz⟩ := D.V_conj _ hvb hne1
  have hxM2 : x ∈ M2 := D.lie.cent_t hx
  have hcX : b2 ⟨x, hxM2⟩ ∈ locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) :=
    mem_locX.2 ⟨⟨x, hxM2⟩, Subgroup.mem_centralizer_singleton_iff.1 hx, rfl⟩
  have hvc : b2 vb = b2 ⟨x, hxM2⟩ * amalgamMap b1 b2 z * (b2 ⟨x, hxM2⟩)⁻¹ := by
    have h1 : amalgamMap b1 b2 (vb : Mb) = b2 vb := amalgamMap_of_mem₂ b1 b2 C.agree vb.2
    rw [← h1, hxz, psi_conj₂ C hxM2 (D.lie.T_le₂ D.lie.z_mem),
      amalgamMap_of_mem₂ b1 b2 C.agree hxM2]
  have hci := locX_comm_t D C ((locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)).inv_mem hcX)
  have hg' : (b2 ⟨x, hxM2⟩)⁻¹ * g * amalgamMap b1 b2 t =
      amalgamMap b1 b2 t * ((b2 ⟨x, hxM2⟩)⁻¹ * g) := by
    calc (b2 ⟨x, hxM2⟩)⁻¹ * g * amalgamMap b1 b2 t
        = (b2 ⟨x, hxM2⟩)⁻¹ * (g * amalgamMap b1 b2 t) := mul_assoc _ _ _
      _ = (b2 ⟨x, hxM2⟩)⁻¹ * (amalgamMap b1 b2 t * g) := by rw [hg]
      _ = ((b2 ⟨x, hxM2⟩)⁻¹ * amalgamMap b1 b2 t) * g := (mul_assoc _ _ _).symm
      _ = (amalgamMap b1 b2 t * (b2 ⟨x, hxM2⟩)⁻¹) * g := by rw [hci]
      _ = amalgamMap b1 b2 t * ((b2 ⟨x, hxM2⟩)⁻¹ * g) := mul_assoc _ _ _
  have hu' : ((b2 ⟨x, hxM2⟩)⁻¹ * g)⁻¹ * amalgamMap b1 b2 z * ((b2 ⟨x, hxM2⟩)⁻¹ * g) ∈
      locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) := by
    have : ((b2 ⟨x, hxM2⟩)⁻¹ * g)⁻¹ * amalgamMap b1 b2 z * ((b2 ⟨x, hxM2⟩)⁻¹ * g) =
        g⁻¹ * (b2 ⟨x, hxM2⟩ * amalgamMap b1 b2 z * (b2 ⟨x, hxM2⟩)⁻¹) * g := by group
    rw [this, ← hvc]
    exact hu
  have h2 := (locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem)).mul_mem hcX
    (locX_fix_z D C hb hnc hg' hu')
  simpa using h2

end Fixed

end CFSG.Quasithin
