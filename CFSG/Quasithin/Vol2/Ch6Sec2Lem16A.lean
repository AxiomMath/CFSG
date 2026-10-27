module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem15C
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem6B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem normalizer_inf_ch616 (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11)
    (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G} (hv : v ∈ V) {g : G}
    (hg : g ∈ hCh611 T)
    (hgk : ∀ k : ℕ, (v * (g⁻¹ * v * g)) ^ 2 ^ k ∉
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)) :
    V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) = V ⊓ uCh611 T L V ∧
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) = conjSubgroup (V ⊓ uCh611 T L V) g ∧
    ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup V g) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := uCh611 T L V with hUdef
  set C := centralizerMod (zCh611 T) (hCh611 T) U with hCdef
  set Vg := conjSubgroup V g with hVg
  set VU := V ⊓ U with hVU
  set VUg := conjSubgroup VU g with hVUg
  set X := V ⊔ Vg with hX
  have hV := h.toHyp611.isElemAbelian
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV ha hb
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hVU8 : Nat.card VU = 8 := by
    have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have hcommVU : ∀ x ∈ V, ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ VU := by
    intro x hx u hu
    have := hVUc (Subgroup.commutator_mem_commutator hx hu)
    rwa [commutatorElement_def] at this
  have hgU : g ∈ Subgroup.normalizer (U : Set G) := hCh611_le_normalizer_u T L V hg
  have hUg : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.mp hgU u).mp hu
  have hUg' : ∀ u ∈ U, g⁻¹ * u * g ∈ U := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).mp hu
    simpa using this
  have hcommVUg : ∀ y ∈ Vg, ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ VUg := by
    intro y hy u hu
    rw [hVUg, mem_conjSubgroup_iff]
    rw [hVg, mem_conjSubgroup_iff] at hy
    have h1 := hcommVU _ hy _ (hUg u hu)
    have e : g * (y * u * y⁻¹ * u⁻¹) * g⁻¹ =
        g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  have hVUgU : VUg ≤ U := fun y hy => by
    rw [hVUg, mem_conjSubgroup_iff] at hy
    have := hUg' _ hy.2
    simpa [mul_assoc] using this
  have hVUgVg : VUg ≤ Vg := fun y hy => by
    rw [hVUg, mem_conjSubgroup_iff] at hy
    rw [hVg, mem_conjSubgroup_iff]
    exact hy.1
  have hN1 : VU ≤ Subgroup.normalizer (Vg : Set G) := by
    intro x hx
    refine mem_normalizer_of_forall_conj_mem_of_le fun y hy => ?_
    have h1 := hcommVUg y hy x hx.2
    have h2 : x * y * x⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ * y := by group
    rw [h2]
    exact Vg.mul_mem (Vg.inv_mem (hVUgVg h1)) hy
  have hN2 : VUg ≤ Subgroup.normalizer (V : Set G) := by
    intro y hy
    refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
    have h1 := hcommVU x hx y (hVUgU hy)
    have h2 : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
    rw [h2]
    exact V.mul_mem (V.inv_mem h1.1) hx
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hVg2 : IsPGroup 2 Vg := by
    rw [hVg]
    exact hV2.map _
  have hnot2 : ¬ IsPGroup 2 X := by
    intro hX2
    obtain ⟨k, hk⟩ := hX2 ⟨v * (g⁻¹ * v * g), X.mul_mem (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right (by rw [hVg, mem_conjSubgroup_iff]; simpa [mul_assoc] using hv))⟩
    apply hgk k
    have : (v * (g⁻¹ * v * g)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact C.one_mem
  have hVgcard : Nat.card Vg = 16 := by rw [hVg, card_conjSubgroup, hV16]
  have hVUgcard : Nat.card VUg = 8 := by rw [hVUg, card_conjSubgroup, hVU8]
  refine ⟨?_, ?_, hnot2⟩
  · symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hN1)
    have hlt' : V ⊓ Subgroup.normalizer (Vg : Set G) < V := by
      refine lt_of_le_of_ne inf_le_left fun he => hnot2 ?_
      exact IsPGroup.to_sup_of_normal_right' hV2 hVg2 (he ▸ inf_le_right)
    have h1 := Subgroup.card_lt_of_lt hlt'
    have h3 : 8 ∣ Nat.card ↥(V ⊓ Subgroup.normalizer (Vg : Set G)) :=
      hVU8 ▸ Subgroup.card_dvd_of_le (le_inf inf_le_left hN1)
    rw [hVU8]
    obtain ⟨c, hc⟩ := h3
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  · symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf hVUgVg hN2)
    have hlt' : Vg ⊓ Subgroup.normalizer (V : Set G) < Vg := by
      refine lt_of_le_of_ne inf_le_left fun he => hnot2 ?_
      exact IsPGroup.to_sup_of_normal_left' hV2 hVg2 (he ▸ inf_le_right)
    have h1 := Subgroup.card_lt_of_lt hlt'
    have h3 : 8 ∣ Nat.card ↥(Vg ⊓ Subgroup.normalizer (V : Set G)) :=
      hVUgcard ▸ Subgroup.card_dvd_of_le (le_inf hVUgVg hN2)
    rw [hVUgcard]
    obtain ⟨c, hc⟩ := h3
    rcases c with _ | _ | c
    · omega
    · omega
    · omega

theorem pair_data_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) {g : G} (hg : g ∈ hCh611 T)
    (hgk : ∀ k : ℕ, (v * (g⁻¹ * v * g)) ^ 2 ^ k ∉
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)) :
    (conjSubgroup (V ⊓ uCh611 T L V) g ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (conjSubgroup (V ⊓ uCh611 T L V) g) = 4 ∧
      CFSG.IsExtraspecial 2 ↥((V ⊓ uCh611 T L V) ⊔ conjSubgroup (V ⊓ uCh611 T L V) g) ∧
      Nat.card ↥((V ⊓ uCh611 T L V) ⊔ conjSubgroup (V ⊓ uCh611 T L V) g) = 2 ^ 5 ∧
      (V ⊓ uCh611 T L V) ⊔ conjSubgroup (V ⊓ uCh611 T L V) g ≤ uCh611 T L V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU', hA', hnot2⟩ :=
    h.normalizer_inf_ch616 h6210 h6211 h6212 hlt hv hg hgk
  set U := uCh611 T L V with hUdef
  set VU := V ⊓ U with hVU
  set X := V ⊔ conjSubgroup V g with hX
  obtain ⟨-, ⟨D, hDX, hXD, hDext, φ, hφs, hφk⟩, hO, hOU⟩ :=
    h.two_six_ch615 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hg hgk
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hVU8 : Nat.card VU = 8 := by
    have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  have hVgcard : Nat.card (conjSubgroup V g) = 16 := by rw [card_conjSubgroup, hV16]
  have hVUgcard : Nat.card (conjSubgroup VU g) = 8 := by rw [card_conjSubgroup, hVU8]
  have hU2 : (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)).relIndex V = 2 := by
    rw [hU']
    have h1 := Subgroup.relIndex_mul_card VU V
    rw [inf_of_le_left inf_le_left, hVU8, hV16] at h1
    omega
  have hA2 : (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (conjSubgroup V g) = 2 := by
    rw [hA']
    have hle : conjSubgroup VU g ≤ conjSubgroup V g := conjSubgroup_mono_left g inf_le_left
    have h1 := Subgroup.relIndex_mul_card (conjSubgroup VU g) (conjSubgroup V g)
    rw [inf_of_le_left hle, hVUgcard, hVgcard] at h1
    omega
  rcases h626 G T M L V h g hA2 hU2 with ⟨-, -, -, -, hp⟩ | ⟨h4, -⟩
  · exact absurd hp hnot2
  rw [hA'] at h4
  have hD32 : Nat.card D = 2 ^ 5 := by rw [hDext.2.1]
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 5) hD32
  have hDO : D ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hDX hXD hD2
  have hOD : pCoreOf 2 X ≤ D := by
    have hφO := le_ker_of_normal_two_ch615 (pCoreOf_le 2 X)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) (pCoreOf_isPGroup 2 X) φ hφs
    intro w hw
    have h1 : (⟨w, pCoreOf_le 2 X hw⟩ : ↥X) ∈ φ.ker := hφO w hw
    rw [hφk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hOeq : pCoreOf 2 X = D := le_antisymm hOD hDO
  rw [hO, hOeq]
  exact ⟨h4, hDext.1, hD32, hOeq ▸ hOU⟩

theorem inf_centerOf_eq_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    V ⊓ centerOf (uCh611 T L V) = zCh611 T := by
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h h331 h432 h512 h614 h615
  have hZc : ∀ z ∈ zCh611 T, ∀ u ∈ uCh611 T L V, u * z = z * u := fun z hz u hu =>
    (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm
  have hcomm : ∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
    fun a ha b hb => h.comm_mem_ch615 h331 h432 h512 h614 h615 ha hb
  have hZZS : zCh611 T ≤ ch6ZS T L V := h.omega_le_ZS h331 h432 h512 h614 h615
  have hZSU : ch6ZS T L V ≤ uCh611 T L V := le_conjClosure _ _
  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615 h6210 h6211 h6212 hlt
  obtain ⟨g, hg, hgk⟩ := h.exists_not_two_ch615 h6210 hv
    (h.not_mem_C_ch615 h6210 h6211 h6212 hlt hv hvU)
  obtain ⟨-, hDes, -, hDU⟩ :=
    h.pair_data_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hg hgk
  obtain ⟨-, -, hcenD⟩ := extraspecial_facts_ch615 hZ2 hDU hZc hcomm hDes
  refine le_antisymm (fun x hx => hcenD x (Subgroup.mem_sup_left ⟨hx.1, hx.2.1⟩) hx.2) ?_
  refine le_inf (hZZS.trans inf_le_left) fun z hz =>
    ⟨hZSU (hZZS hz), Subgroup.mem_centralizer_iff.mpr fun u hu => hZc z hz u hu⟩

theorem mem_centralizer_of_comm_mem_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h512 : Stmt5_1_2) (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) {u : G} (hu : u ∈ uCh611 T L V)
    (hvu : v * u * v⁻¹ * u⁻¹ ∈ zCh611 T) : u ∈ Subgroup.centralizer (V : Set G) := by
  classical
  by_contra huC
  set U := uCh611 T L V with hUdef
  set Z := zCh611 T with hZdef
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  have hV := h.toHyp611.isElemAbelian
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hVU8 : Nat.card ↥(V ⊓ U) = 8 := by
    have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  have hZc : ∀ z ∈ Z, ∀ x : G, x ∈ hCh611 T → x * z = z * x := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp hx z hz).symm
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    h.toHyp611.T_le_normalizer (h.uCh611_le_T h331 h432 h512 h614 h615 hu)
  have hall : ∀ x ∈ V, x * u * x⁻¹ * u⁻¹ ∈ Z := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact h.comm_mem_ch615 h331 h432 h512 h614 h615 hxU hu
    · have hw : v⁻¹ * x ∈ V ⊓ U := by
        have hidx : (V ⊓ U).relIndex V = 2 := by
          have h1 := Subgroup.relIndex_mul_card (V ⊓ U) V
          rw [inf_of_le_left inf_le_left, hVU8, hV16] at h1
          omega
        exact mul_mem_of_relIndex_two_ch626 hidx (V.inv_mem hv) hx
          (fun h' => hvU (by simpa using (V ⊓ U).inv_mem h' |>.2))
          (fun h' => hxU h'.2)
      have h1 := h.comm_mem_ch615 h331 h432 h512 h614 h615 hw.2 hu
      have hc : v * ((v⁻¹ * x) * u * (v⁻¹ * x)⁻¹ * u⁻¹) =
          ((v⁻¹ * x) * u * (v⁻¹ * x)⁻¹ * u⁻¹) * v := hZc _ h1 v (h.V_le_hCh611 hv)
      have e : x * u * x⁻¹ * u⁻¹ =
          ((v⁻¹ * x) * u * (v⁻¹ * x)⁻¹ * u⁻¹) * (v * u * v⁻¹ * u⁻¹) := by
        calc x * u * x⁻¹ * u⁻¹ = v * ((v⁻¹ * x) * u * (v⁻¹ * x)⁻¹ * u⁻¹) * u * v⁻¹ * u⁻¹ := by
              group
          _ = ((v⁻¹ * x) * u * (v⁻¹ * x)⁻¹ * u⁻¹) * v * u * v⁻¹ * u⁻¹ := by rw [hc]
          _ = _ := by group
      rw [e]
      exact Z.mul_mem h1 hvu
  have hZV : Z ≤ V := (h.omega_le_ZS h331 h432 h512 h614 h615).trans inf_le_left
  have h8 := card_le_mul_card_centralizer_ch626 (K := V) (B := Z) (a := u) hall
    (fun k hk b hb => hZc b hb k (h.V_le_hCh611 hk))
    (fun b hb b' hb' => B2F.isElemAbelian_comm hV (hZV hb) (hZV hb'))
  have h4' := h.card_fix_le_four h432 huN huC
  rw [hV16, hZ2] at h8
  omega

theorem inf_centralizer_eq_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) {g : G} (hg : g ∈ hCh611 T)
    (hgk : ∀ k : ℕ, (v * (g⁻¹ * v * g)) ^ 2 ^ k ∉
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)) :
    conjSubgroup (V ⊓ uCh611 T L V) g ⊓ Subgroup.centralizer (V : Set G) = zCh611 T := by
  obtain ⟨h4, -⟩ := h.pair_data_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv
    hg hgk
  set U := uCh611 T L V with hUdef
  set Z := zCh611 T with hZdef
  set A := conjSubgroup (V ⊓ U) g with hAdef
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  have hVU8 : Nat.card ↥(V ⊓ U) = 8 := by
    have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  have hA8 : Nat.card A = 8 := by rw [hAdef, card_conjSubgroup, hVU8]
  have hZc : ∀ z ∈ Z, ∀ x : G, x ∈ hCh611 T → x * z = z * x := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp hx z hz).symm
  have hZA : Z ≤ A ⊓ Subgroup.centralizer (V : Set G) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hZc z hz x (h.V_le_hCh611 hx)⟩
    show z ∈ conjSubgroup (V ⊓ U) g
    rw [mem_conjSubgroup_iff]
    have hgz : g * z * g⁻¹ = z := by rw [hZc z hz g hg, mul_inv_cancel_right]
    rw [hgz]
    exact ⟨((h.omega_le_ZS h331 h432 h512 h614 h615).trans inf_le_left) hz,
      (le_conjClosure (ch6ZS T L V) (hCh611 T)) (h.omega_le_ZS h331 h432 h512 h614 h615 hz)⟩
  have h1 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
  rw [inf_of_le_left inf_le_left, h4, hA8] at h1
  exact (Subgroup.eq_of_le_of_card_ge hZA (by rw [hZ2]; omega)).symm

theorem comm_not_mem_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) {g : G} (hg : g ∈ hCh611 T)
    (hgk : ∀ k : ℕ, (v * (g⁻¹ * v * g)) ^ 2 ^ k ∉
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V))
    {a : G} (ha : a ∈ conjSubgroup (V ⊓ uCh611 T L V) g) (haZ : a ∉ zCh611 T) :
    v * a * v⁻¹ * a⁻¹ ∉ zCh611 T := by
  intro hva
  have hAU : conjSubgroup (V ⊓ uCh611 T L V) g ≤ uCh611 T L V :=
    le_sup_right.trans (h.pair_data_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv
      hg hgk).2.2.2
  have haC := h.mem_centralizer_of_comm_mem_ch616 h331 h432 h512 h614 h615 h6210 h6211 h6212 hlt
    hv hvU (hAU ha) hva
  have := h.inf_centralizer_eq_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hg
    hgk
  exact haZ (this ▸ (⟨ha, haC⟩ : a ∈ conjSubgroup (V ⊓ uCh611 T L V) g ⊓
    Subgroup.centralizer (V : Set G)))

end Hyp6Sec2

end CFSG.Quasithin.H13
