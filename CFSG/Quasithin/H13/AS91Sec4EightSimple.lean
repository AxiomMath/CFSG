module

public import CFSG.Quasithin.H13.AS91Sec4EightHc
public import CFSG.Quasithin.H13.AS91Sec4EightS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Qs

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)
  (hHat : HatM22SmallModules)

@[expose] noncomputable def Qs : Subgroup ↥D.Mb := D.img (h.setting.QG ⊔ D.E)

theorem QE_le_N : h.setting.QG ⊔ D.E ≤ normalizer (D.E : Set G) :=
  sup_le D.QG_le_N le_normalizer

include hOut hTw hHat

theorem card_Qs : Nat.card D.Qs = 64 := by
  have h1 := D.card_img hOut hTw hHat D.QE_le_N le_sup_right
  rw [D.card_E hOut hTw, D.card_QE hOut hTw] at h1
  rw [Qs]
  omega

theorem Qs_comm_sq {φ ψ : ↥D.Mb} (hφ : φ ∈ D.Qs) (hψ : ψ ∈ D.Qs) :
    φ * ψ * φ⁻¹ * ψ⁻¹ = 1 ∧ φ * φ = 1 := by
  obtain ⟨x, hxN, hx, rfl⟩ := D.mem_img.mp hφ
  obtain ⟨y, hyN, hy, rfl⟩ := D.mem_img.mp hψ
  obtain ⟨h1, h2⟩ := D.QE_elem hOut hTw hx hy
  constructor
  · have hc : x * y * x⁻¹ * y⁻¹ ∈ normalizer (D.E : Set G) :=
      mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
    have e1 : D.toMb ⟨x * y * x⁻¹ * y⁻¹, hc⟩ =
        D.toMb ⟨x, hxN⟩ * D.toMb ⟨y, hyN⟩ * (D.toMb ⟨x, hxN⟩)⁻¹ * (D.toMb ⟨y, hyN⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [← e1]
    exact (D.toMb_eq_one_iff hOut hTw hHat _).mpr h1
  · have e1 : D.toMb ⟨x * x, mul_mem hxN hxN⟩ = D.toMb ⟨x, hxN⟩ * D.toMb ⟨x, hxN⟩ := by
      rw [← map_mul]
      rfl
    rw [← e1]
    exact (D.toMb_eq_one_iff hOut hTw hHat _).mpr h2

theorem Qs_comm {φ ψ : ↥D.Mb} (hφ : φ ∈ D.Qs) (hψ : ψ ∈ D.Qs) : φ * ψ = ψ * φ :=
  (mul_comm_iff_mul_inv_mul_inv_eq_one φ ψ).mpr (D.Qs_comm_sq hOut hTw hHat hφ hψ).1

omit hOut hTw hHat in
theorem tb_mem_Qs : D.tb ∈ D.Qs :=
  D.toMb_mem_img (D.QG_le_N D.q0e_mem_QG) (le_sup_left (a := h.setting.QG) D.q0e_mem_QG)

theorem Qs_le_Cb : D.Qs ≤ D.Cb := fun φ hφ =>
  mem_centralizer_singleton_iff.mpr (D.Qs_comm hOut hTw hHat hφ D.tb_mem_Qs)

theorem isElemAbelian_Qs : IsElemAbelian 2 D.Qs := by
  refine ⟨⟨⟨fun a b => Subtype.ext (D.Qs_comm hOut hTw hHat a.2 b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact (D.Qs_comm_sq hOut hTw hHat hx hx).2

theorem conj_tb_mem_Qs {φ : ↥D.Mb} (hφ : φ ∈ D.Mz) : φ * D.tb * φ⁻¹ ∈ D.Qs := by
  obtain ⟨m, hm, rfl⟩ := (D.mem_Mz_iff hOut hTw).mp hφ
  have hq := D.q0e_mem_QG
  have hc : m * D.q0e * m⁻¹ ∈ h.setting.QG := h.setting.conj_mem_QG (D.G13_le_M hm) hq
  have e1 : D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ * D.tb *
      (D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩)⁻¹ =
      D.toMb ⟨m * D.q0e * m⁻¹, D.QG_le_N hc⟩ := by
    rw [tb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e1]
  exact D.toMb_mem_img _ (le_sup_left (a := h.setting.QG) hc)

end Qs

section Orbit45

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem ncard_conj_Mz :
    {ψ : ↥D.Mb | ∃ φ ∈ D.Mz, ψ = φ * D.tb * φ⁻¹}.ncard = 45 := by
  letI : MulAction ↥D.Mz ↥D.Mb :=
    MulAction.compHom ↥D.Mb ((MulAut.conj : ↥D.Mb →* MulAut ↥D.Mb).comp D.Mz.subtype)
  have hsmul : ∀ (φ : ↥D.Mz) (x : ↥D.Mb), φ • x = (φ : ↥D.Mb) * x * (φ : ↥D.Mb)⁻¹ :=
    fun _ _ => rfl
  have horb : MulAction.orbit ↥D.Mz D.tb = {ψ : ↥D.Mb | ∃ φ ∈ D.Mz, ψ = φ * D.tb * φ⁻¹} := by
    ext ψ
    constructor
    · rintro ⟨φ, rfl⟩
      exact ⟨φ, φ.2, (hsmul φ D.tb)⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ, hφ⟩, hsmul _ _⟩
  have hstab : Nat.card (MulAction.stabilizer ↥D.Mz D.tb) = 3072 := by
    rw [← D.card_C3 hOut hTw hHat]
    refine Nat.card_congr
      { toFun := fun φ => ⟨φ.1.1, φ.1.2, mem_centralizer_singleton_iff.mpr ?_⟩
        invFun := fun φ => ⟨⟨φ.1, φ.2.1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h1 : (φ.1 : ↥D.Mb) * D.tb * (φ.1 : ↥D.Mb)⁻¹ = D.tb := (hsmul φ.1 D.tb).symm.trans φ.2
      calc (φ.1 : ↥D.Mb) * D.tb = (φ.1 : ↥D.Mb) * D.tb * (φ.1 : ↥D.Mb)⁻¹ * φ.1 := by group
        _ = D.tb * φ.1 := by rw [h1]
    · change (⟨φ.1, φ.2.1⟩ : ↥D.Mz) • D.tb = D.tb
      rw [hsmul]
      have h1 := mem_centralizer_singleton_iff.mp φ.2.2
      change (φ : ↥D.Mb) * D.tb = D.tb * φ at h1
      rw [h1, mul_inv_cancel_right]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥D.Mz D.tb)
  rw [MulAction.index_stabilizer, hstab, D.card_Mz hOut hTw hHat, horb] at h1
  omega

theorem Qs_le_of_normal {N : Subgroup ↥D.Mb} (hN : N.Normal) (htN : D.tb ∈ N) : D.Qs ≤ N := by
  have hsub : {ψ : ↥D.Mb | ∃ φ ∈ D.Mz, ψ = φ * D.tb * φ⁻¹} ⊆ ((N ⊓ D.Qs : Subgroup ↥D.Mb) : Set ↥D.Mb) := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨hN.conj_mem _ htN φ, D.conj_tb_mem_Qs hOut hTw hHat hφ⟩
  have h45 : 45 ≤ Nat.card (N ⊓ D.Qs : Subgroup ↥D.Mb) := by
    have h1 : Nat.card (N ⊓ D.Qs : Subgroup ↥D.Mb) =
        ((N ⊓ D.Qs : Subgroup ↥D.Mb) : Set ↥D.Mb).ncard := (Nat.card_coe_set_eq _).symm.trans rfl
    rw [h1, ← D.ncard_conj_Mz hOut hTw hHat]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hdvd : Nat.card (N ⊓ D.Qs : Subgroup ↥D.Mb) ∣ 64 := by
    rw [← D.card_Qs hOut hTw hHat]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h64 : Nat.card (N ⊓ D.Qs : Subgroup ↥D.Mb) = 64 := by
    rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp (show _ ∣ 2 ^ 6 from hdvd) with
      ⟨k, hk, hk'⟩
    interval_cases k <;> simp_all
  have heq : N ⊓ D.Qs = D.Qs :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h64, D.card_Qs hOut hTw hHat])
  rw [← heq]
  exact inf_le_left

end Orbit45

section Normal

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem Cb_le_of_normal {N : Subgroup ↥D.Mb} (hN : N.Normal) (htN : D.tb ∈ N) : D.Cb ≤ N := by
  obtain ⟨e⟩ := D.nonempty_cb_mulEquiv hOut hTw hHat
  have hQN := D.Qs_le_of_normal hOut hTw hHat hN htN
  have hQC := D.Qs_le_Cb hOut hTw hHat
  set K : Subgroup CFSG.Quasithin.A94.L52.Hc := (N.subgroupOf D.Cb).map e.toMonoidHom with hK
  have hKn : K.Normal := (hN.subgroupOf D.Cb).map e.toMonoidHom e.surjective
  set X : Subgroup CFSG.Quasithin.A94.L52.Hc := (D.Qs.subgroupOf D.Cb).map e.toMonoidHom with hX
  have hQab := D.isElemAbelian_Qs hOut hTw hHat
  have hXab : IsElemAbelian 2 X := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change (a : CFSG.Quasithin.A94.L52.Hc) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact D.Qs_comm hOut hTw hHat (Subgroup.mem_subgroupOf.mp ha') (Subgroup.mem_subgroupOf.mp hb')
    · obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_pow]
      have : y' ^ 2 = 1 := by
        apply Subtype.ext
        rw [pow_two]
        exact (D.Qs_comm_sq hOut hTw hHat (Subgroup.mem_subgroupOf.mp hy')
          (Subgroup.mem_subgroupOf.mp hy')).2
      rw [this, map_one]
  have hXc : Nat.card X = 64 := by
    rw [hX, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, D.card_Qs hOut hTw hHat]
  have hXK : X ≤ K := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQN (Subgroup.mem_subgroupOf.mp hx))
  have htop := HcFacts.eq_top_of_E64_le hKn hXab hXc hXK
  intro c hc
  have hmem : e ⟨c, hc⟩ ∈ K := by rw [htop]; trivial
  obtain ⟨x, hx, hxe⟩ := hmem
  have : x = ⟨c, hc⟩ := e.injective hxe
  have hx' := Subgroup.mem_subgroupOf.mp hx
  rwa [this] at hx'

theorem inf_Bb_eq_bot {N : Subgroup ↥D.Mb} (hodd : Odd (Nat.card N)) : N ⊓ D.Bb = ⊥ := by
  have h1 : Nat.card (N ⊓ D.Bb : Subgroup ↥D.Mb) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (N ⊓ D.Bb : Subgroup ↥D.Mb) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← D.card_Bb hOut hTw hHat]
    exact Subgroup.card_dvd_of_le inf_le_right
  rw [← Subgroup.card_eq_one]
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases k with _ | k
  · simpa using hk'
  · exfalso
    rw [hk'] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega)).trans h1))

theorem eq_one_of_comm_tb {N : Subgroup ↥D.Mb} (hN : N.Normal) (hodd : Odd (Nat.card N))
    {n : ↥D.Mb} (hnN : n ∈ N) (hnt : n * D.tb = D.tb * n) : n = 1 := by
  have hnC : n ∈ D.Cb := mem_centralizer_singleton_iff.mpr hnt
  have hNB := D.inf_Bb_eq_bot hOut hTw hHat hodd
  have hnB : ∀ b ∈ D.Bb, n * b = b * n := by
    intro b hb
    have hcN : n * b * n⁻¹ * b⁻¹ ∈ N := by
      have h1 := hN.conj_mem n⁻¹ (inv_mem hnN) b
      have h2 : n * b * n⁻¹ * b⁻¹ = n * (b * n⁻¹ * b⁻¹) := by group
      rw [h2]
      exact mul_mem hnN h1
    have hcB : n * b * n⁻¹ * b⁻¹ ∈ D.Bb := mul_mem (D.conj_mem_Bb hnC hb) (inv_mem hb)
    have hbot : n * b * n⁻¹ * b⁻¹ ∈ (N ⊓ D.Bb : Subgroup ↥D.Mb) := ⟨hcN, hcB⟩
    rw [hNB, mem_bot] at hbot
    exact (mul_comm_iff_mul_inv_mul_inv_eq_one n b).mpr hbot
  have hnBb := D.mem_Bb_of_centralizes hOut hTw hHat hnC hnB
  have hbot : n ∈ (N ⊓ D.Bb : Subgroup ↥D.Mb) := ⟨hnN, hnBb⟩
  rwa [hNB, mem_bot] at hbot

theorem conj_inv_of_odd {N : Subgroup ↥D.Mb} (hN : N.Normal) (hodd : Odd (Nat.card N))
    {g x : ↥D.Mb} (hx : g * D.tb * g⁻¹ = x) {n : ↥D.Mb} (hnN : n ∈ N) : x * n * x⁻¹ = n⁻¹ := by
  have hx2 : x * x = 1 := by
    rw [← hx]
    have h2 := D.Bb_mul_self hOut hTw hHat (D.tb_mem_Bb hOut hTw hHat)
    calc g * D.tb * g⁻¹ * (g * D.tb * g⁻¹) = g * (D.tb * D.tb) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hfix : ∀ m ∈ N, m * x = x * m → m = 1 := by
    intro m hmN hmx
    have hm' : g⁻¹ * m * g ∈ N := by
      have := hN.conj_mem m hmN g⁻¹
      rwa [inv_inv] at this
    have hcomm : (g⁻¹ * m * g) * D.tb = D.tb * (g⁻¹ * m * g) := by
      rw [← hx] at hmx
      calc g⁻¹ * m * g * D.tb = g⁻¹ * (m * (g * D.tb * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * D.tb * g⁻¹) * m) * g := by rw [hmx]
        _ = D.tb * (g⁻¹ * m * g) := by group
    have h1 := D.eq_one_of_comm_tb hOut hTw hHat hN hodd hm' hcomm
    calc m = g * (g⁻¹ * m * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  let φ : ↥N →* ↥N := (MulAut.conjNormal x : MulAut ↥N).toMonoidHom
  have hφ : ∀ m : ↥N, ((φ m : ↥N) : ↥D.Mb) = x * m * x⁻¹ := fun m => MulAut.conjNormal_apply x m
  have hfpf : MonoidHom.FixedPointFree φ := by
    intro m hm
    have h1 := congrArg Subtype.val hm
    rw [hφ] at h1
    apply Subtype.ext
    refine hfix m m.2 ?_
    calc (m : ↥D.Mb) * x = x * m * x⁻¹ * x := by rw [h1]
      _ = x * m := by group
  have hinv : Function.Involutive φ := by
    intro m
    apply Subtype.ext
    rw [hφ, hφ]
    calc x * (x * (m : ↥D.Mb) * x⁻¹) * x⁻¹ = (x * x) * m * (x * x)⁻¹ := by group
      _ = m := by rw [hx2]; group
  have := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinv) ⟨n, hnN⟩
  have h2 := congrArg Subtype.val this
  rw [hφ] at h2
  exact h2

theorem eq_bot_of_odd {N : Subgroup ↥D.Mb} (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨g₁, -, hg₁⟩ := D.exists_conj_tb' hOut hTw hHat
  obtain ⟨g₂, -, hg₂⟩ := D.exists_conj_tb5 hOut hTw hHat
  have hprod : D.tb * D.tb' = D.toMb ⟨D.rep 5, D.QG_le_N (D.rep_mem 5)⟩ := by
    have hq := D.q0e_mem_QG
    have hr := D.rep_mem 513
    have e1 : D.tb * D.tb' = D.toMb ⟨D.q0e * D.rep 513, D.QG_le_N (mul_mem hq hr)⟩ := by
      rw [tb, tb', ← map_mul]
      rfl
    rw [e1]
    refine D.toMb_QG_eq hOut hTw hHat (mul_mem hq hr) (D.rep_mem 5) ?_
    rw [h.setting.cl_mul hq hr, map_add, q0e, D.ψV_cl_rep, D.ψV_cl_rep, D.ψV_cl_rep, ← vecOf_xor,
      ← vecOf_xor]
    exact (Two.vecOf_mem_W1 (by decide)).mpr (by decide)
  rw [eq_bot_iff]
  intro n hnN
  rw [mem_bot]
  have h1 := D.conj_inv_of_odd hOut hTw hHat hN hodd (g := 1) (x := D.tb) (by group) hnN
  have h2 := D.conj_inv_of_odd hOut hTw hHat hN hodd hg₁ hnN
  have h3 := D.conj_inv_of_odd hOut hTw hHat hN hodd (hg₂.trans hprod.symm) hnN
  have h4 : D.tb * D.tb' * n * (D.tb * D.tb')⁻¹ = n := by
    calc D.tb * D.tb' * n * (D.tb * D.tb')⁻¹ = D.tb * (D.tb' * n * D.tb'⁻¹) * D.tb⁻¹ := by group
      _ = D.tb * n⁻¹ * D.tb⁻¹ := by rw [h2]
      _ = (D.tb * n * D.tb⁻¹)⁻¹ := by group
      _ = n := by rw [h1, inv_inv]
  have hn2 : n * n = 1 := by
    have := h3.symm.trans h4
    calc n * n = n⁻¹⁻¹ * n := by rw [inv_inv]
      _ = 1 := by rw [this, inv_mul_cancel]
  have hdvd2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hn2)
  have hdvdN : orderOf n ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨n, hnN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  have h1n : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · exfalso
      rw [h] at hdvdN
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvdN)
  exact orderOf_eq_one_iff.mp h1n

theorem tb_mem_of_even {N : Subgroup ↥D.Mb} (hN : N.Normal) (h2 : 2 ∣ Nat.card N) : D.tb ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := D.nonempty_cb_mulEquiv hOut hTw hHat
  set F := CFSG.Quasithin.A94.frame0 e (D.orderOf_tb hOut hTw hHat) with hF
  obtain ⟨P, hP⟩ := CFSG.Quasithin.A94.s39_2 F
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  have hxp : IsPGroup 2 (zpowers (x : ↥D.Mb)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥D.Mb Q P
  have hgx : g * x * g⁻¹ ∈ (P : Subgroup ↥D.Mb) := by
    have hle : (zpowers (x : ↥D.Mb)).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup ↥D.Mb) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact Subgroup.map_mono hQ
    exact hle ⟨x, mem_zpowers _, rfl⟩
  haveI : Group.IsNilpotent ↥P := P.isPGroup'.isNilpotent
  haveI := hN.subgroupOf (P : Subgroup ↥D.Mb)
  have hH : N.subgroupOf (P : Subgroup ↥D.Mb) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨g * x * g⁻¹, hgx⟩, Subgroup.mem_subgroupOf.mpr (hN.conj_mem x x.2 g)⟩, fun h1 => ?_⟩
    have h1' : g * (x : ↥D.Mb) * g⁻¹ = 1 := by
      have := congrArg (fun y : ↥(N.subgroupOf (P : Subgroup ↥D.Mb)) => ((y : ↥P) : ↥D.Mb)) h1
      exact this
    have hx1 : (x : ↥D.Mb) = 1 := by
      calc (x : ↥D.Mb) = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1']; group
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hH
  obtain ⟨⟨y, hyH, hyZ⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hyT : (y : ↥D.Mb) ∈ F.T := hP ▸ y.2
  have hc : ∀ w ∈ F.T, (y : ↥D.Mb) * w = w * y := by
    intro w hw
    have := Subgroup.mem_center_iff.mp hyZ ⟨w, hP ▸ hw⟩
    exact (congrArg Subtype.val this).symm
  rcases F.center_T _ hyT hc with h1 | h1
  · exfalso
    apply hy1
    exact Subtype.ext (Subtype.ext h1)
  · rw [← h1]
    exact Subgroup.mem_subgroupOf.mp hyH

theorem isSimpleGroup_Mb : IsSimpleGroup ↥D.Mb where
  exists_pair_ne := ⟨1, D.tb, (D.tb_ne_one hOut hTw hHat).symm⟩
  eq_bot_or_eq_top_of_normal N hN := by
    rcases Nat.even_or_odd (Nat.card N) with he | ho
    · right
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have htN := D.tb_mem_of_even hOut hTw hHat hN (even_iff_two_dvd.mp he)
      have hCN := D.Cb_le_of_normal hOut hTw hHat hN htN
      obtain ⟨e⟩ := D.nonempty_cb_mulEquiv hOut hTw hHat
      set F := CFSG.Quasithin.A94.frame0 e (D.orderOf_tb hOut hTw hHat) with hF
      obtain ⟨P, hP⟩ := CFSG.Quasithin.A94.s39_2 F
      have hPN : (P : Subgroup ↥D.Mb) ≤ N := by
        rw [hP]
        exact F.T_le_H.trans hCN
      haveI := hN
      have htop := Sylow.normalizer_sup_eq_top' P hPN
      have hnorm : normalizer (P : Set ↥D.Mb) ≤ N := by
        intro n hn
        have hn' : n ∈ normalizer (F.T : Set ↥D.Mb) := by
          rw [← hP]
          exact hn
        exact hCN (F.normalizer_T_le_H n hn')
      rwa [sup_eq_right.mpr hnorm] at htop
    · left
      exact D.eq_bot_of_odd hOut hTw hHat hN ho

end Normal

end Data41

end CFSG.Quasithin.H13.AS91
