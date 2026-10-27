module

public import CFSG.Quasithin.H13.L32AC33f
public import CFSG.Quasithin.Background.SzAutBorel
public import CFSG.Quasithin.H13.L32AC33d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace CtxB

variable {K : Subgroup G} {t₀ : G} (C : CtxB T L V H K t₀)
include C

theorem mem_szS1_of_szB1 (hA37 : A37ForSQTK) (h29 : Thm14_7_29)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {e : ℕ}
    (hSz : IsSz e (cStar K)) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1)
    {b : ↥H ⧸ CFSG.pCore 2 ↥H} (hb : b ∈ szB1 T H K) :
    b⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * b *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ ∈ szS1 T H K := by
  have hyH := Setting147.l1H' C.S hy
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) b
  have hβN := C.mem_normalizer_l1_of_szB1 hA37 h29 h1222 h1332 h1334 hb
  have hl : (β : G)⁻¹ * y * β * y⁻¹ ∈ l1 T L V := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hβN) y).mp hy
    rw [inv_inv] at h1
    exact mul_mem h1 (inv_mem hy)
  have hlH : (β : G)⁻¹ * y * β * y⁻¹ ∈ H := Setting147.l1H' C.S hl
  have e1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) β)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) β *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hlH⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hyK := mk_mem_normalizer (y := ⟨y, hyH⟩) C.hKH (C.hyN y hy hy3)
  have hK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hlH⟩ ∈ modO2Image H K := by
    rw [← e1]
    have h1 := (Subgroup.mem_normalizer_iff.mp hyK _).mp hb.2
    have e2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) β)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) β *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) β)⁻¹ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) β *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹) := by group
    rw [e2]
    exact mul_mem (inv_mem hb.2) h1
  obtain ⟨φ⟩ := modO2_mulEquiv C.hK
  have hKsz : IsSz e ↥(modO2Image H K) := isSz_congr ((cStarEquiv K).trans φ) hSz
  have hcop : Nat.Coprime 3 (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hlH⟩)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hK)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (H13.A5.ConfSz.three_not_dvd_card hKsz))
  rw [e1]
  exact ⟨mk_mem_T_of_coprime h1222 h1332 h1334 C.S (l := ⟨_, hlH⟩) hl hcop, hK⟩

theorem centralizes (hSzB : SzAutBorelThree) (hA37 : A37ForSQTK)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {e : ℕ} (hSz : IsSz e (cStar K)) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1)
    {n : ↥H ⧸ CFSG.pCore 2 ↥H} (hn : n ∈ modO2Image H K) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * n *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = n := by
  have hyH := Setting147.l1H' C.S hy
  have hyK := mk_mem_normalizer (y := ⟨y, hyH⟩) C.hKH (C.hyN y hy hy3)
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK
  let α : MulAut ↥(modO2Image H K) :=
    ((MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)).subgroupMap
      (modO2Image H K)).trans (MulEquiv.subgroupCongr hmap)
  have hα : ∀ x : ↥(modO2Image H K), ((α x : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * x *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ := fun x => by
    show (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩))
      (x : ↥H ⧸ CFSG.pCore 2 ↥H) = _
    rw [MulAut.conj_apply]
  obtain ⟨φ⟩ := modO2_mulEquiv C.hK
  have hKsz : IsSz e ↥(modO2Image H K) := isSz_congr ((cStarEquiv K).trans φ) hSz
  have hS := C.isSylowIn_szS1
  have hyb3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩) ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hy3)
  have key : ∀ (m : ℕ) (x : ↥(modO2Image H K)),
      (((α ^ m) x : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ ^ m * x *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ]
      group
  have hα3 : α ^ 3 = 1 := by
    ext x
    rw [key 3 x, hyb3, MulAut.one_apply]
    group
  have hyS := C.mk_l1_mem_normalizer_szS1 h1222 h1332 h1334 hy hy3
  have hmapS : ((hS.toSylow : Subgroup ↥(modO2Image H K))).map α.toMonoidHom =
      (hS.toSylow : Subgroup ↥(modO2Image H K)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      show α s ∈ (szS1 T H K).subgroupOf (modO2Image H K)
      rw [Subgroup.mem_subgroupOf, hα]
      exact (Subgroup.mem_normalizer_iff.mp hyS s).mp (Subgroup.mem_subgroupOf.mp hs)
    · rw [Subgroup.card_map_of_injective α.injective]
  have hB : ∀ b ∈ Subgroup.normalizer
      (((hS.toSylow : Subgroup ↥(modO2Image H K))) : Set ↥(modO2Image H K)),
      b⁻¹ * α b ∈ (hS.toSylow : Subgroup ↥(modO2Image H K)) := by
    intro b hb
    have hbB : (b : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szB1 T H K := by
      refine ⟨mem_normalizer_of_conj_mem_fin fun s hs => ?_, b.2⟩
      have hsK : s ∈ modO2Image H K := hS.le hs
      have h1 := (Subgroup.mem_normalizer_iff.mp hb ⟨s, hsK⟩).mp
        (Subgroup.mem_subgroupOf.mpr hs)
      exact Subgroup.mem_subgroupOf.mp h1
    have h1 := C.mem_szS1_of_szB1 hA37 h29 h1222 h1332 h1334 hSz hy hy3 hbB
    show b⁻¹ * α b ∈ (szS1 T H K).subgroupOf (modO2Image H K)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hα]
    have e1 : (b : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * b *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹) =
        (b : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * b *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ := by group
    rw [e1]
    exact h1
  have h1 := hSzB _ e hKsz hS.toSylow α hα3 hmapS hB
  have h2 := congrArg (fun f : MulAut ↥(modO2Image H K) =>
    ((f ⟨n, hn⟩ : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H)) h1
  simp only [MulAut.one_apply] at h2
  rw [hα] at h2
  exact h2

theorem comm (hSzB : SzAutBorelThree) (hA37 : A37ForSQTK)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {e : ℕ} (hSz : IsSz e (cStar K)) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) {k : G}
    (hk : k ∈ K) : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
  mem_O2H_of_commute ⟨y, Setting147.l1H' C.S hy⟩ ⟨k, C.hKH hk⟩ (comm_of_conj_eq
    (C.centralizes hSzB hA37 h29 h1222 h1332 h1334 hSz hy hy3
      (mem_modO2Image'.mpr ⟨⟨k, C.hKH hk⟩, hk, rfl⟩)))

end CtxB

end CFSG.Quasithin.H13.L32A.C
