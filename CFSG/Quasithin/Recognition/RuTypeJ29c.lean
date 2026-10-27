module

public import CFSG.Quasithin.Recognition.RuTypeJ29b
public import CFSG.Quasithin.Recognition.RuTypeAutA6b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem exists_Ls_mul
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {k : G} (hk : k ∈ Cen s) :
    ∃ l ∈ Ls s, ∃ t ∈ M.S3, k = l * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P, hP⟩ := M.lemma_J27_10 hs hs1
  set N := (Ls s).subgroupOf (Cen s) with hNdef
  have hNn : N.Normal := CFSG.GorensteinWalter.pResidualOf_subgroupOf_normal (Cen s) 2
  have hQ : IsPGroup 2 (Cen s ⧸ N) :=
    CFSG.GorensteinWalter.isPGroup_quotient_pResidualOf (Cen s) 2 Nat.prime_two
  let P' : Sylow 2 (Cen s ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have htop : (P' : Subgroup (Cen s ⧸ N)) = ⊤ := (P'.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have hk' : (QuotientGroup.mk' N ⟨k, hk⟩ : Cen s ⧸ N) ∈ (P' : Subgroup _) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective, hP] at hk'
  obtain ⟨t, ht, htk⟩ := hk'
  have htS3 : (t : G) ∈ M.S3 := by
    rw [← M.centralizer_H_eq_S3 hs hs1]
    exact Subgroup.mem_subgroupOf.mp ht
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at htk
  have hl' : (t : G)⁻¹ * k ∈ Ls s := by simpa using Subgroup.mem_subgroupOf.mp htk
  have hl : (t : G) * ((t : G)⁻¹ * k) * (t : G)⁻¹ ∈ Ls s := by
    have := hNn.conj_mem ⟨_, mul_mem (inv_mem t.2) hk⟩ (Subgroup.mem_subgroupOf.mpr hl') t
    simpa using Subgroup.mem_subgroupOf.mp this
  refine ⟨_, hl, t, htS3, ?_⟩
  group

theorem exists_Ls_conj_z
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {w : G} (hw : IsConj M.z w)
    (hws : w * s = s * w) : ∃ l ∈ Ls s, l * M.z * l⁻¹ = w := by
  obtain ⟨k, hks, hkz⟩ := M.exists_centralizer_conj_z hs hs1 hw hws
  obtain ⟨l, hl, t, ht, rfl⟩ := M.exists_Ls_mul hs hs1 (mem_Cen.mpr hks)
  have htz : (t : G) * M.z = M.z * t := (M.mem_H_iff_comm.mp (M.S3_le_H ht)).symm
  refine ⟨l, hl, ?_⟩
  rw [← hkz]
  calc l * M.z * l⁻¹ = l * (t * M.z * t⁻¹) * l⁻¹ := by rw [htz, mul_inv_cancel_right]
    _ = l * t * M.z * (l * t)⁻¹ := by group

theorem exists_inv_five_Cen
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ∃ w y : G, w ∈ Cen s ∧ y ∈ Cen s ∧ w * w = 1 ∧ IsConj M.z w ∧ orderOf y = 5 ∧
      w * y * w⁻¹ = y⁻¹ := by
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  obtain ⟨d, hd, hdB, hd2, -⟩ := M.exists_lift_inv e AutA6.dInv_mem_autA6
    AutA6.dInv_mul_self AutA6.dInv_not_mem_m10
  have hx5 : A6Models.tAdd * A6Models.tSq * A6Models.tInv ∈ A6Models.psl29 :=
    mul_mem (mul_mem Out21.A6.tAdd_mem_psl29 Out21.A6.tSq_mem_psl29) Out21.A6.tInv_mem_psl29
  obtain ⟨y5, hy5GB, hy5o, hy5c, hy5ρ⟩ := M.exists_comm_five_of_ρ e d hx5 x5_pow_five x5_ne_one
    (by rw [hd]; exact AutA6.dInv_comm)
  obtain ⟨xw, hxw⟩ := (M.ρ_bijective e).2
    ⟨AutA6.wInv, A6Facts.psl29_le_autA6 AutA6.wInv_mem_psl29⟩
  obtain ⟨w0, rfl⟩ := QuotientGroup.mk_surjective xw
  have hw0B : (w0 : G) ∈ M.GB := by
    rw [← M.ρ_mk_mem_m10_iff e w0, hxw]
    exact Out21.A6.psl29_le_m10 AutA6.wInv_mem_psl29
  have hw02 : (w0 : G) * w0 ∈ M.B := by
    have h1 : (QuotientGroup.mk (w0 * w0) : M.XP) = 1 := by
      apply M.ρ_injective e
      rw [QuotientGroup.mk_mul, map_mul, hxw, map_one]
      exact Subtype.ext AutA6.wInv_mul_self
    rw [QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  set w1 : G := (w0 : G) * w0 * w0 with hw1def
  have hw1B : w1 ∈ M.GB := mul_mem (mul_mem hw0B hw0B) hw0B
  have hw12 : w1 * w1 = 1 := by
    have h3 := M.pow_three_of_mem_B hw02
    calc w1 * w1 = ((w0 : G) * w0) ^ 3 := by rw [hw1def, pow_three]; group
      _ = 1 := h3
  have hw1q : (QuotientGroup.mk (⟨w1, M.GB_le_GP hw1B⟩ : M.GP) : M.XP) = QuotientGroup.mk w0 := by
    rw [M.mk_eq_mk_iff_XP]
    show ((w0 : G) * w0 * w0)⁻¹ * w0 ∈ M.B
    have : ((w0 : G) * w0 * w0)⁻¹ * w0 = ((w0 : G) * w0)⁻¹ := by group
    rw [this]
    exact inv_mem hw02
  have hw1ρ : ((M.ρ e (QuotientGroup.mk (⟨w1, M.GB_le_GP hw1B⟩ : M.GP)) : A6Models.autA6) :
      Equiv.Perm (Fin 10)) = AutA6.wInv := by rw [hw1q, hxw]
  have hcomm_of : ∀ {a b : G} (ha : a ∈ M.GP) (hb : b ∈ M.GP),
      ((M.ρ e (QuotientGroup.mk (⟨a, ha⟩ : M.GP)) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk (⟨b, hb⟩ : M.GP)) : A6Models.autA6) : Equiv.Perm (Fin 10)) =
        ((M.ρ e (QuotientGroup.mk (⟨b, hb⟩ : M.GP)) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk (⟨a, ha⟩ : M.GP)) : A6Models.autA6) : Equiv.Perm (Fin 10)) →
      (b⁻¹ * a * b)⁻¹ * a ∈ M.B := by
    intro a b ha hb h
    have hq : (QuotientGroup.mk (⟨b, hb⟩⁻¹ * ⟨a, ha⟩ * ⟨b, hb⟩ : M.GP) : M.XP) =
        QuotientGroup.mk ⟨a, ha⟩ := by
      apply M.ρ_injective e
      apply Subtype.ext
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [mul_assoc, h]
      group
    exact M.mk_eq_mk_iff_XP.mp hq
  have hw1d : w1 * d = d * w1 := by
    have h := hcomm_of (M.GB_le_GP hw1B) d.2 (by rw [hw1ρ, hd]; exact AutA6.wInv_comm_dInv)
    set u := (d : G)⁻¹ * w1 * d with hudef
    have hu2 : u * u = 1 := by
      rw [hudef]
      calc (d : G)⁻¹ * w1 * d * ((d : G)⁻¹ * w1 * d) = (d : G)⁻¹ * (w1 * w1) * d := by group
        _ = 1 := by rw [hw12]; group
    have huB : u ∈ M.GB := by
      have := M.conj_mem_GB (inv_mem d.2) hw1B
      simpa [hudef] using this
    set b := u⁻¹ * w1 with hbdef
    have hb1 : b = 1 := by
      have hbc : Commute u b := (Subgroup.mem_centralizer_iff.mp huB b h).symm
      have h1 : w1 = u * b := by rw [hbdef]; group
      have h2 : (u * b) * (u * b) = 1 := by rw [← h1, hw12]
      have h3 : b * b = 1 := by
        calc b * b = (u * u) * (b * b) := by rw [hu2, one_mul]
          _ = (u * b) * (u * b) := by
            rw [show (u * b) * (u * b) = u * (b * u) * b by group, ← hbc.eq]; group
          _ = 1 := h2
      have h4 := M.pow_three_of_mem_B h
      calc b = b ^ 3 * (b * b)⁻¹ := by group
        _ = 1 := by rw [h4, h3]; group
    have : u = w1 := by
      have h1 : w1 = u * b := by rw [hbdef]; group
      rw [h1, hb1, mul_one]
    rw [hudef] at this
    calc w1 * d = d * ((d : G)⁻¹ * w1 * d) := by group
      _ = d * w1 := by rw [this]
  have hw1y : w1 * y5 * w1⁻¹ = y5⁻¹ := by
    have hy5GP : y5 ∈ M.GP := M.GB_le_GP hy5GB
    have hq : (QuotientGroup.mk (⟨w1, M.GB_le_GP hw1B⟩ * ⟨y5, hy5GP⟩ *
        ⟨w1, M.GB_le_GP hw1B⟩⁻¹ : M.GP) : M.XP) = QuotientGroup.mk (⟨y5, hy5GP⟩⁻¹ : M.GP) := by
      apply M.ρ_injective e
      apply Subtype.ext
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hw1ρ, hy5ρ hy5GP]
      exact AutA6.wInv_inv_x5
    have hb := M.mk_eq_mk_iff_XP.mp hq
    set b := (w1 * y5 * w1⁻¹)⁻¹ * y5⁻¹ with hbdef
    have hb' : b ∈ M.B := by simpa [hbdef] using hb
    have hconj : w1 * y5 * w1⁻¹ ∈ M.GB := mul_mem (mul_mem hw1B hy5GB) (inv_mem hw1B)
    have hc : Commute (w1 * y5 * w1⁻¹) b :=
      (Subgroup.mem_centralizer_iff.mp hconj b hb').symm
    have hy55 : y5 ^ 5 = 1 := by rw [← hy5o]; exact pow_orderOf_eq_one y5
    have h5 : (w1 * y5 * w1⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hy55]
      group
    have hy5inv : y5⁻¹ = (w1 * y5 * w1⁻¹) * b := by rw [hbdef]; group
    have h55 : (y5⁻¹) ^ 5 = 1 := by
      rw [inv_pow, ← hy5o, pow_orderOf_eq_one, inv_one]
    rw [hy5inv, hc.mul_pow, h5, one_mul] at h55
    have h3 := M.pow_three_of_mem_B hb'
    have hb1 : b = 1 := by
      calc b = (b ^ 3) ^ 2 * (b ^ 5)⁻¹ := by group
        _ = 1 := by rw [h3, h55]; group
    calc w1 * y5 * w1⁻¹ = (w1 * y5 * w1⁻¹) * b := by rw [hb1, mul_one]
      _ = y5⁻¹ := hy5inv.symm
  have hdinv : ((M.ρ e (QuotientGroup.mk d) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∉
      A6Facts.s6 := by rw [hd]; exact AutA6.dInv_not_mem_s6
  have hsd := (M.outer_inv_classes e d hdB hd2).2 hdinv s hs hs1
  obtain ⟨g, hg⟩ := isConj_iff.mp hsd
  have hzw1 : IsConj M.z w1 := by
    obtain ⟨k, -, hk⟩ := M.lemma_J27_9 hw1B (by rw [pow_two]; exact hw12) (fun h => by
      apply AutA6.wInv_ne_one
      rw [← hw1ρ]
      have : (⟨w1, M.GB_le_GP hw1B⟩ : M.GP) = 1 := Subtype.ext h
      rw [this, QuotientGroup.mk_one, map_one]
      rfl)
    exact isConj_iff.mpr ⟨k, hk⟩
  refine ⟨g⁻¹ * w1 * g, g⁻¹ * y5 * g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_Cen]
    rw [← hg] at hw1d
    calc g⁻¹ * w1 * g * s = g⁻¹ * (w1 * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * w1) * g := by rw [hw1d]
      _ = s * (g⁻¹ * w1 * g) := by group
  · rw [mem_Cen]
    rw [← hg] at hy5c
    calc g⁻¹ * y5 * g * s = g⁻¹ * (y5 * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * y5) * g := by rw [hy5c]
      _ = s * (g⁻¹ * y5 * g) := by group
  · calc g⁻¹ * w1 * g * (g⁻¹ * w1 * g) = g⁻¹ * (w1 * w1) * g := by group
      _ = 1 := by rw [hw12]; group
  · exact hzw1.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  · rw [show g⁻¹ * y5 * g = g⁻¹ * y5 * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq]
    exact hy5o
  · calc g⁻¹ * w1 * g * (g⁻¹ * y5 * g) * (g⁻¹ * w1 * g)⁻¹ = g⁻¹ * (w1 * y5 * w1⁻¹) * g := by
          group
      _ = (g⁻¹ * y5 * g)⁻¹ := by rw [hw1y]; group

theorem not_Ls_le_L
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : ¬ Ls s ≤ M.L := by
  intro hle
  obtain ⟨w, y, hw, hy, hw2, hwz, hy5, hwy⟩ := M.exists_inv_five_Cen hs hs1
  obtain ⟨l, hl, hlz⟩ := M.exists_Ls_conj_z hs hs1 hwz (mem_Cen.mp hw)
  have hwV : w ∈ ruV M.L := by
    rw [← hlz]
    exact M.toRuData.conj_mem_V (hle hl) M.z_mem_V
  have hyL : y ∈ M.L := hle (mem_Ls_of_odd hy (by rw [hy5]; decide))
  have hyV : y⁻¹ * y⁻¹ ∈ ruV M.L := by
    have h1 : y * w⁻¹ * y⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V hyL (inv_mem hwV)
    have e : y⁻¹ * y⁻¹ = w * (y * w⁻¹ * y⁻¹) := by
      calc y⁻¹ * y⁻¹ = (w * y * w⁻¹) * y⁻¹ := by rw [hwy]
        _ = w * (y * w⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem hwV h1
  have h4 : (y⁻¹ * y⁻¹) ^ 2 = 1 := M.sq_eq_one_of_V hyV
  have hy51 : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have : y = 1 := by
    calc y = y ^ 5 * ((y⁻¹ * y⁻¹) ^ 2) := by group
      _ = 1 := by rw [hy51, h4, one_mul]
  rw [this, orderOf_one] at hy5
  norm_num at hy5

theorem mem_V_of_inv_CL
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hxL : x ∈ M.L)
    (hxs : x ∈ Cen s) (hxLs : x ∈ Ls s) (hx2 : x ^ 2 = 1) : x ∈ ruV M.L := by
  obtain ⟨k, hk⟩ := M.θ_mem_of_comm hs hs1 (l := ⟨x, hxL⟩) (mem_Cen.mp hxs)
  have h1 : SL3.c0 ^ k.val = 1 := by
    have h7 : orderOf (SL3.c0 ^ k.val) ∣ 7 := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, SL3.c0_pow_seven, one_pow])
    have h2 : orderOf (SL3.c0 ^ k.val) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [← hk, ← map_pow, show (⟨x, hxL⟩ : M.L) ^ 2 = 1 from Subtype.ext hx2, map_one])
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h7 h2)
  have hker : (⟨x, hxL⟩ : M.L) ∈ M.θ.ker := by rw [MonoidHom.mem_ker, hk, h1]
  rw [M.θ_ker, Subgroup.mem_subgroupOf] at hker
  have hS3 : x ∈ M.S3 := by
    rw [← M.centralizer_eq_S3 hs hs1]
    exact ⟨hker, hxs⟩
  exact M.mem_V_of_S1_sq (M.mem_S1_of_mem_Ls hs hs1 hS3 hxLs) hx2

theorem isStronglyEmbedded_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    CFSG.BenderSuzuki.IsStronglyEmbedded ((M.L ⊓ Ls s).subgroupOf (Ls s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply M.not_Ls_le_L hs hs1
    intro x hx
    have : (⟨x, hx⟩ : Ls s) ∈ (M.L ⊓ Ls s).subgroupOf (Ls s) := by
      rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  · refine ⟨⟨M.z, M.S1_le_Ls hs hs1 (M.V_le_S1 M.z_mem_V)⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨M.toRuData.V_le_L M.z_mem_V,
        M.S1_le_Ls hs hs1 (M.V_le_S1 M.z_mem_V)⟩
    · refine ⟨fun h => M.z_ne_one (congrArg Subtype.val h), Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact M.z_sq
  · intro g hg x hx hxg hinv
    have hgLs := g.2
    have hxLs := x.2
    obtain ⟨hx1, hx2⟩ := hinv
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hx2' : (x : G) ^ 2 = 1 := by
      have := congrArg Subtype.val hx2
      simpa using this
    have hxLG := (Subgroup.mem_subgroupOf.mp hx).1
    have hxV : (x : G) ∈ ruV M.L :=
      M.mem_V_of_inv_CL hs hs1 hxLG (Ls_le_Cen s hxLs) hxLs hx2'
    have hgx : (g : G) * x * (g : G)⁻¹ ∈ M.L := by
      have h := hxg
      rw [CFSG.BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy,
        Subgroup.mem_map] at h
      obtain ⟨y, hy, hyx⟩ := h
      have hy' : g * x * g⁻¹ = y := by rw [← hyx]; simp [mul_assoc]
      rw [← hy'] at hy
      have := (Subgroup.mem_subgroupOf.mp hy).1
      simpa using this
    have hgxLs : (g : G) * x * (g : G)⁻¹ ∈ Ls s := mul_mem (mul_mem hgLs hxLs) (inv_mem hgLs)
    have hgxV : (g : G) * x * (g : G)⁻¹ ∈ ruV M.L :=
      M.mem_V_of_inv_CL hs hs1 hgx (Ls_le_Cen s hgxLs) hgxLs (by rw [conj_pow, hx2']; group)
    apply hg
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, hgLs⟩
    have hgL : (g : G)⁻¹ ∈ M.L := by
      rw [M.one.eq_normalizer]
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      have hvLs : v ∈ Ls s := M.S1_le_Ls hs hs1 (M.V_le_S1 hv)
      have hmem : (g : G)⁻¹ * v * (g : G)⁻¹⁻¹ ∈ Ls s :=
        mul_mem (mul_mem (inv_mem hgLs) hvLs) (inv_mem (inv_mem hgLs))
      have hcomm : (g : G)⁻¹ * v * (g : G)⁻¹⁻¹ * x = x * ((g : G)⁻¹ * v * (g : G)⁻¹⁻¹) := by
        have hc : v * ((g : G) * x * (g : G)⁻¹) = ((g : G) * x * (g : G)⁻¹) * v :=
          M.V_comm_S hgxV (M.toRuData.V_le_S hv)
        calc (g : G)⁻¹ * v * (g : G)⁻¹⁻¹ * x =
            (g : G)⁻¹ * (v * ((g : G) * x * (g : G)⁻¹)) * g := by group
          _ = (g : G)⁻¹ * (((g : G) * x * (g : G)⁻¹) * v) * g := by rw [hc]
          _ = x * ((g : G)⁻¹ * v * (g : G)⁻¹⁻¹) := by group
      have hS1 := M.mem_S1_of_comm_V hs hs1 hxV hx1' hmem hcomm
      refine M.mem_V_of_S1_sq hS1 ?_
      rw [conj_pow, M.sq_eq_one_of_V hv]
      group
    have := inv_mem hgL
    rwa [inv_inv] at this

end RuDataM

end CFSG.Quasithin.RuType
