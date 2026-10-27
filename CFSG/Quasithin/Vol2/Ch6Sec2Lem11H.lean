module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11G
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5G
public import CFSG.Quasithin.Vol2.Ch11SecD556A
public import CFSG.Quasithin.H13.U3S1348H
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11A
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11B
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

abbrev zCh611 (T : Subgroup G) : Subgroup G := quasithinOmegaOneCenter T

abbrev hCh611 (T : Subgroup G) : Subgroup G := Subgroup.centralizer (zCh611 T : Set G)

abbrev uCh611 (T L V : Subgroup G) : Subgroup G := conjClosure (ch6ZS T L V) (hCh611 T)

omit [Finite G] in
theorem hCh611_le_normalizer_u (T L V : Subgroup G) :
    hCh611 T ≤ Subgroup.normalizer (uCh611 T L V : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] in
theorem hCh611_le_normalizer_z (T : Subgroup G) :
    hCh611 T ≤ Subgroup.normalizer (zCh611 T : Set G) :=
  Subgroup.centralizer_le_normalizer _

noncomputable abbrev rhoCh611 (T L V : Subgroup G)
    [((zCh611 T).subgroupOf (uCh611 T L V)).Normal] :
    ↥(hCh611 T) →* MulAut (↥(uCh611 T L V) ⧸ (zCh611 T).subgroupOf (uCh611 T L V)) :=
  actQuot (uCh611 T L V) (zCh611 T) (hCh611 T) (hCh611_le_normalizer_u T L V)
    (hCh611_le_normalizer_z T)

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem uCh611_le_h (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) : uCh611 T L V ≤ hCh611 T := by
  obtain ⟨⟨-, hUQ, -⟩, -, -, -⟩ := h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  exact hUQ.trans (pCoreOf_le 2 _)

theorem normal_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    ((zCh611 T).subgroupOf (uCh611 T L V)).Normal := by
  have hUH := h.uCh611_le_h h331 h432 h512 h614 h615
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hg : (g : G) ∈ hCh611 T := hUH g.2
  have := Subgroup.mem_centralizer_iff.mp hg x hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← this, mul_inv_cancel_right]
  exact hx

theorem commMod_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) : CommModCh611 (uCh611 T L V) (zCh611 T) := by
  obtain ⟨⟨-, hUQ, hcomm⟩, -, -, -⟩ := h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  refine ⟨fun a ha b hb => ?_⟩
  have := Subgroup.commutator_mem_commutator ha (hUQ hb)
  have h1 := hcomm this
  rwa [commutatorElement_def] at h1

theorem stage_g31_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2)
    [((zCh611 T).subgroupOf (uCh611 T L V)).Normal] [CommModCh611 (uCh611 T L V) (zCh611 T)] :
    Nat.card (↥(uCh611 T L V) ⧸ (zCh611 T).subgroupOf (uCh611 T L V)) = 8 ∧
      (rhoCh611 T L V).range = ⊤ ∧
      ∀ x : ↥(uCh611 T L V) ⧸ (zCh611 T).subgroupOf (uCh611 T L V), x ^ 2 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := zCh611 T with hZdef
  set H := hCh611 T with hHdef
  set U := uCh611 T L V with hUdef
  set ρ := rhoCh611 T L V with hρ
  set Gm := ρ.range with hGm
  set ZS := ch6ZS T L V with hZSdef
  obtain ⟨hVC, -, hVUc, hCQ⟩ := h.step_a_ch611 h331 h432 h512 h614 h615 h6210 h4
  obtain ⟨-, -, hO2', -, -⟩ := h6210 G T M L V h
  have hV := h.toHyp611.isElemAbelian
  have hZZS : Z ≤ ZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card ZS = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hZSU : ZS ≤ U := le_conjClosure _ _
  have hUH : U ≤ H := h.uCh611_le_h h331 h432 h512 h614 h615
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hTH : T ≤ H := fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  have hVH : V ≤ H := h.toHyp611.le_T.trans hTH
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hCh611_le_normalizer_u T L V
  set X₀ := quotSub U Z ZS with hX₀def
  have hX₀ : Nat.card X₀ = 2 := by
    have := card_quotSub (U := U) hZZS hZSU
    rw [← hX₀def, hZ2, hZS4] at this
    omega
  have hO2 : pCoreOf 2 Gm = ⊥ := pCoreOf_range_actQuot_eq_bot hO2'
  have hmapX : ∀ (k : ↥H) (X : Subgroup G),
      (quotSub U Z X).map (ρ k).toMonoidHom = quotSub U Z (conjSubgroup X (k : G)⁻¹) :=
    fun k X => map_actQuot_quotSub k X
  have hZconj : ∀ k : ↥H, Z ≤ conjSubgroup ZS (k : G)⁻¹ := by
    intro k z hz
    rw [mem_conjSubgroup_iff, inv_inv]
    have hkz := Subgroup.mem_centralizer_iff.mp k.2 z hz
    rw [mul_assoc, hkz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hZZS hz
  have hconjU : ∀ k : ↥H, conjSubgroup ZS (k : G)⁻¹ ≤ U := by
    intro k x hx
    rw [mem_conjSubgroup_iff, inv_inv] at hx
    have := (Subgroup.mem_normalizer_iff.mp (hHU k.2) _).mp (hZSU hx)
    simpa [mul_assoc] using this
  set Δ₀ := orbitCh611 Gm X₀ with hΔ₀
  have hmemΔ : ∀ k : ↥H, quotSub U Z (conjSubgroup ZS (k : G)⁻¹) ∈ Δ₀ :=
    fun k => ⟨ρ k, ⟨k, rfl⟩, hmapX k ZS⟩
  have htop : g31V Δ₀ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using QuotientGroup.induction_on with
    | H u =>
    obtain ⟨u, hu⟩ := u
    have key : ∀ (y : G) (hy : y ∈ U),
        ((⟨y, hy⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U) ∈ g31V Δ₀ := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨k, hk, z, hz, rfl⟩ := hx
        have hmem : ((⟨k * z * k⁻¹, Subgroup.subset_closure ⟨k, hk, z, hz, rfl⟩⟩ : ↥U) :
            ↥U ⧸ Z.subgroupOf U) ∈
            quotSub U Z (conjSubgroup ZS (⟨k, hk⟩ : ↥H)⁻¹) := by
          rw [mem_quotSub_iff (hZconj ⟨k, hk⟩)]
          rw [mem_conjSubgroup_iff]
          have e : ((⟨k, hk⟩ : ↥H) : G)⁻¹ * (k * z * k⁻¹) * ((⟨k, hk⟩ : ↥H) : G)⁻¹⁻¹ = z := by
            simp only [inv_inv]
            group
          rw [e]
          exact hz
        exact le_g31V (hmemΔ ⟨k, hk⟩) hmem
      | one => exact (g31V Δ₀).one_mem
      | mul x y hx hy ihx ihy =>
        have e : ((⟨x * y, U.mul_mem hx hy⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U) =
            ((⟨x, hx⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U) * ((⟨y, hy⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U) :=
          rfl
        rw [e]
        exact (g31V Δ₀).mul_mem ihx ihy
      | inv x hx ihx =>
        have e : ((⟨x⁻¹, U.inv_mem hx⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U) =
            ((⟨x, hx⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U)⁻¹ := rfl
        rw [e]
        exact (g31V Δ₀).inv_mem ihx
    exact key u hu
  have hsq : ∀ x : ↥U ⧸ Z.subgroupOf U, x ^ 2 = 1 := by
    have hle : g31V Δ₀ ≤ (powMonoidHom 2 : (↥U ⧸ Z.subgroupOf U) →* _).ker := by
      refine iSup₂_le fun X hX x hx => ?_
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h2 : Nat.card X = 2 := card_of_mem_orbitCh611 hX₀ hX
      have := Subgroup.orderOf_dvd_natCard X hx
      rw [h2] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    intro x
    have := hle (htop ▸ Subgroup.mem_top x)
    rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this
  set ψ : ↥V →* MulAut (↥U ⧸ Z.subgroupOf U) := ρ.comp (Subgroup.inclusion hVH) with hψ
  set RV := ψ.range with hRV
  have hψapp : ∀ v : ↥V, ψ v = ρ (Subgroup.inclusion hVH v) := fun v => rfl
  have hRVA : RV ≤ transvGroup Gm X₀ := by
    rintro r ⟨v, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨⟨Subgroup.inclusion hVH v, rfl⟩, fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [hψapp, actQuot_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        mem_quotSub_iff hZZS]
      have := hVUc (Subgroup.commutator_mem_commutator v.2 u.2)
      rw [commutatorElement_def] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      exact this
  have hker : ψ.ker = (V ⊓ centralizerMod Z H U).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψapp, ← mem_centralizerMod_iff_actQuot']
    exact ⟨fun h1 => ⟨v.2, h1⟩, fun h1 => h1.2⟩
  have hRV4 : Nat.card RV = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hVC, hZS4,
      hV16, ← hRV] at h1
    omega
  have h9 := stmt6_2_9 h331 h432 h512 h614 h615 G T M L V h
  have hstab : ∀ g ∈ Gm, X₀.map g.toMonoidHom = X₀ → ∀ r ∈ RV, g * r * g⁻¹ ∈ RV := by
    rintro g ⟨k, rfl⟩ hgX r ⟨v, rfl⟩
    have h1 : quotSub U Z (conjSubgroup ZS (k : G)⁻¹) = quotSub U Z ZS :=
      (hmapX k ZS).symm.trans hgX
    have h2 : conjSubgroup ZS (k : G)⁻¹ = ZS :=
      eq_of_quotSub_eq (hZconj k) hZZS (hconjU k) hZSU h1
    have hkN : (k : G)⁻¹ ∈ Subgroup.normalizer (ZS : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.mp h2
    have hkN' : (k : G) ∈ Subgroup.normalizer (ZS : Set G) := by
      simpa using Subgroup.inv_mem _ hkN
    have hkV : (k : G) ∈ Subgroup.normalizer (V : Set G) := by
      have : (k : G) ∈ H ⊓ Subgroup.normalizer (ZS : Set G) := ⟨k.2, hkN'⟩
      rw [← h9.2.1] at this
      exact this.2
    have hkv : (k : G) * v * (k : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hkV v).mp v.2
    refine ⟨⟨_, hkv⟩, ?_⟩
    rw [hψapp, hψapp]
    have e : Subgroup.inclusion hVH ⟨_, hkv⟩ = k * Subgroup.inclusion hVH v * k⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
  have hodd : Odd (Nat.card Δ₀) := by
    set NZ := (Subgroup.normalizer (ZS : Set G)).subgroupOf H with hNZ
    have hconjeq : ∀ a b : ↥H, conjSubgroup ZS (a : G)⁻¹ = conjSubgroup ZS (b : G)⁻¹ ↔
        a⁻¹ * b ∈ NZ := by
      intro a b
      rw [hNZ, Subgroup.mem_subgroupOf]
      constructor
      · intro hab
        have h1 := congrArg (fun A => conjSubgroup A (a : G)) hab
        simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
        have h2 : ((b : G)⁻¹ * a) ∈ Subgroup.normalizer (ZS : Set G) :=
          conjSubgroup_eq_iff_mem_normalizer.mp h1.symm
        have h3 := Subgroup.inv_mem _ h2
        simpa using h3
      · intro hab
        have h1 : conjSubgroup ZS ((a⁻¹ * b : ↥H) : G) = ZS :=
          conjSubgroup_eq_iff_mem_normalizer.mpr hab
        calc conjSubgroup ZS (a : G)⁻¹
            = conjSubgroup (conjSubgroup ZS ((a⁻¹ * b : ↥H) : G)) (b : G)⁻¹ := by
              rw [conjSubgroup_conjSubgroup]
              congr 1
              simp
          _ = conjSubgroup ZS (b : G)⁻¹ := by rw [h1]
    let f : ↥H → ↥Δ₀ := fun k => ⟨X₀.map (ρ k).toMonoidHom, ⟨ρ k, ⟨k, rfl⟩, rfl⟩⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨X, g, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    have hfib : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ NZ := by
      intro a b
      rw [← hconjeq]
      constructor
      · intro hab
        have h1 : X₀.map (ρ a).toMonoidHom = X₀.map (ρ b).toMonoidHom := congrArg Subtype.val hab
        rw [hX₀def, hmapX, hmapX] at h1
        exact eq_of_quotSub_eq (hZconj a) (hZconj b) (hconjU a) (hconjU b) h1
      · intro hab
        apply Subtype.ext
        show X₀.map (ρ a).toMonoidHom = X₀.map (ρ b).toMonoidHom
        rw [hX₀def, hmapX, hmapX, hab]
    rw [card_eq_index_of_fibers_ch625 f hsurj hfib]
    have hTN : T.subgroupOf H ≤ NZ := fun t ht => by
      rw [hNZ, Subgroup.mem_subgroupOf]
      exact h.toHyp611Nat.T_le_normalizer_ZS (Subgroup.mem_subgroupOf.mp ht)
    have hTodd : ¬ 2 ∣ (T.subgroupOf H).index := by
      intro h2
      apply h.sylow.2
      rw [← Subgroup.relIndex_mul_index hTH]
      exact Dvd.dvd.mul_right h2 _
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact fun h2 => hTodd (h2.trans (Subgroup.index_dvd_of_le hTN))
  have hA : 4 ≤ Nat.card (transvGroup Gm X₀) := hRV4 ▸ Subgroup.card_le_of_le hRVA
  obtain ⟨D⟩ := g31_apply_ch611 hG31 hsq hO2 hX₀ hA
  have h8 := D.card_V0_eq_eight hsq hX₀ htop hRVA hRV4 hstab
  have hsodd := D.odd_s_of_odd hsq hX₀ h8 hodd
  have hs3 : ¬ 3 ≤ D.s := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite (MulAut (↥U ⧸ Z.subgroupOf U)) :=
      Finite.of_injective (fun g : MulAut (↥U ⧸ Z.subgroupOf U) => (g : _ → _))
        DFunLike.coe_injective
    obtain ⟨E, hEGm, hEab, hE27⟩ := D.exists_elemAbelian_27 hsq htop h3
    have hE3 : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
    obtain ⟨r, hr⟩ := hE3.exists_card_eq
    have hr3 : 3 ≤ r := by
      by_contra hcon
      push Not at hcon
      have : 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set E' := E.subgroupOf Gm with hE'
    have hE'card : Nat.card E' = 3 ^ r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEGm).toEquiv, hr]
    have hE'ab : IsElemAbelian 3 E' := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have := hEab.1.is_comm.comm ⟨(a : ↥Gm), a.2⟩ ⟨(b : ↥Gm), b.2⟩
        have this' : ((a : ↥Gm) : MulAut (↥U ⧸ Z.subgroupOf U)) * ((b : ↥Gm) : MulAut _) =
            ((b : ↥Gm) : MulAut _) * ((a : ↥Gm) : MulAut _) := congrArg Subtype.val this
        exact Subtype.ext (Subtype.ext this')
      · apply Subtype.ext
        simpa using hEab.2 _ hx
    have hZne : Z ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hZ2
      omega
    have hZp : IsPGroup 2 Z := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      have h1 : orderOf (x : G) ∣ 2 := by
        have := Subgroup.orderOf_dvd_natCard (s := Z) x.2
        rwa [hZ2] at this
      simpa using orderOf_dvd_iff_pow_eq_one.mp h1
    have hev : CFSG.Assembly.evenRank G ≤ 2 := h.qtke.2.2
    have hrank : ∀ F : Subgroup G, F ≤ H → IsElemAbelian 3 F → ∀ r, Nat.card F = 3 ^ r →
        r ≤ 2 := fun F hFH hFab r hFr =>
      Vol2.Ch11.SecD.le_two_of_elemAbelian hev hZne hZp Nat.prime_three (by norm_num)
        (hFH.trans (hCh611_le_normalizer_z T)) hFab hFr
    have hkerρ : ∀ x : ↥H, ρ.rangeRestrict x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1 := by
      intro x hx
      have h1 : ρ x = 1 := congrArg Subtype.val hx
      have hxC := (mem_centralizerMod_iff_actQuot' x).mpr h1
      rw [hCQ] at hxC
      obtain ⟨i, hi⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hxC⟩
      exact ⟨i, Subtype.ext (by simpa using congrArg Subtype.val hi)⟩
    have := U3.le_two_of_elemAbelian_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      hkerρ Nat.prime_three (by norm_num) hrank hE'ab hE'card
    omega
  have hs1 : D.s = 1 := by
    obtain ⟨k, hk⟩ := hsodd
    omega
  obtain ⟨hV0top, hGmtop⟩ := D.eq_top_of_s_eq_one htop hs1
  refine ⟨?_, hGmtop, hsq⟩
  rw [← h8, hV0top, Subgroup.card_top]

end Hyp6Sec2

end CFSG.Quasithin.H13
