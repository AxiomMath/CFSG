module

public import CFSG.Quasithin.H13.L32A722a
public import CFSG.Quasithin.H13.L32AS4c
public import CFSG.Quasithin.H13.L32A714S4
public import CFSG.Quasithin.H13.L32AS4a
public import CFSG.Quasithin.H13.L32AS4b

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

omit [Finite G] in
theorem le_normalizer_e :
    L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤
      Subgroup.normalizer ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_commutator (le_normalizer_conjClosure V _ hx.2)
    (le_normalizer_pCoreOf_sup T L hx.1)

omit [Finite G] in
theorem l1_le_l (D : Data T L V θ c) : L32A.l1 T L V ≤ L := fun _ hx => (D.l1_le hx).1

theorem e_le_u (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ fsuU T V :=
  commutator_fsuU_le C.setting.hyp D.mod

theorem r_le_s (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ L32A.sL T L V :=
  conjClosure_mono (e_le_u C D) le_rfl

theorem r_comm (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {a b : G}
    (ha : a ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)
    (hb : b ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) : a * b = b * a := by
  have ha' := C.r_center ha
  have hbS : b ∈ L32A.sL T L V := (r_le_s C D hb)
  exact (Subgroup.mem_centralizer_iff.mp ha'.2 b hbS).symm

theorem r_sq (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {a : G}
    (ha : a ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) : a ^ 2 = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, -, e, he, rfl⟩ := hx
    have he2 : e ^ 2 = 1 := F7.isElemAbelian_pow_eq_one D.elem_u (e_le_u C D he)
    rw [conj_pow, he2]
    group
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (show Commute x y from r_comm C D hx hy) 2), ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

theorem r_le_normalizer_v (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ Subgroup.normalizer (V : Set G) := by
  have hVR : V ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    C.v_le_e.trans (le_conjClosure _ _)
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    rw [r_comm C D ha (hVR hv), mul_inv_cancel_right]
    exact hv
  · intro hv
    have h1 := r_comm C D ha (hVR hv)
    have e : a * v * a⁻¹ = v := by
      calc a * v * a⁻¹ = a⁻¹ * (a * (a * v * a⁻¹)) := by group
        _ = a⁻¹ * ((a * v * a⁻¹) * a) := by rw [h1]
        _ = v := by group
    rwa [e] at hv

theorem comm_mem_v_of_ker (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) (l : ↥L)
    (hl : θ l = 1) {x : G} (hx : x ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) :
    (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ V := by
  have hlQ : (l : G) ∈ pCoreOf 2 (L ⊔ T) := D.cent_le ⟨l.2, (D.ker l).mp hl⟩
  have h1 := Subgroup.commutator_mem_commutator hlQ hx
  rw [Subgroup.commutator_comm, C.rq] at h1
  simpa [commutatorElement_def] using h1

theorem secMod_r (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    SecMod L (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) V θ := by
  have hVR : V ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    C.v_le_e.trans (le_conjClosure _ _)
  refine SecMod.of_nontrivial hVR (le_normalizer_conjClosure _ _)
    (le_sup_left.trans D.norm_v) (fun a ha b hb => ?_) (fun a ha => ?_) D.surj
    (fun l hl x hx => comm_mem_v_of_ker C D l hl hx) ?_
  · rw [r_comm C D ha hb, mul_inv_cancel_right, mul_inv_cancel]
    exact V.one_mem
  · rw [r_sq C D ha]
    exact V.one_mem
  ·
    obtain ⟨e, he, heV⟩ : ∃ e ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, e ∉ V := by
      by_contra h
      push Not at h
      have h1 : V.relIndex ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = 1 := Subgroup.relIndex_eq_one.mpr h
      rw [C.relIndex_ve] at h1
      norm_num at h1
    by_contra hall
    push Not at hall
    apply heV
    refine C.fpf_e e he fun l hl => ?_
    exact hall ⟨l, l1_le_l D hl⟩ e (le_conjClosure _ _ he)

theorem exists_gen_e (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ∃ m ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, m ∉ V ∧
      ∀ l : ↥L, θ l ∈ H6.borel → (l : G) * m * (l : G)⁻¹ * m⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup G := (H6.borel.comap θ).map L.subtype with hB
  have hBmem : ∀ {b : G}, b ∈ B → ∃ l : ↥L, θ l ∈ H6.borel ∧ (l : G) = b := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨l, hl, rfl⟩
  have hEU := e_le_u C D
  have hEp : IsPGroup 2 ↥⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := fun x => ⟨1, Subtype.ext (by
    simpa using F7.isElemAbelian_pow_eq_one D.elem_u (hEU x.2))⟩
  have hBE : B ≤ Subgroup.normalizer ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := hBmem hb
    exact le_normalizer_e ⟨l.2, (D.ll l).mp (Subgroup.mem_inf.mp hl).2⟩
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := by
    intro b hb
    obtain ⟨l, -, rfl⟩ := hBmem hb
    exact (le_sup_left.trans D.norm_v) l.2
  have hEV : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ Subgroup.normalizer (V : Set G) :=
    (le_conjClosure _ L).trans (r_le_normalizer_v C D)
  have hne : V ≠ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
    intro h
    have h1 := C.relIndex_ve
    rw [← h, Subgroup.relIndex_self] at h1
    norm_num at h1
  obtain ⟨m, hmE, hmV, hmB⟩ := exists_mem_fix_mod C.v_le_e hne D.borel_two hEp hBE hBV hEV
  exact ⟨m, hmE, hmV, fun l hl => hmB l (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)⟩

theorem e_eq_closure (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {m : G}
    (hm : m ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) (hmV : m ∉ V) :
    ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ =
      Subgroup.closure ({y | ∃ a ∈ L32A.l1 T L V, a * m * a⁻¹ = y} ∪ (V : Set G)) :=
  eq_closure_of_fpf C.v_le_e ((le_conjClosure _ L).trans (r_le_normalizer_v C D))
    (fun _ hx => le_normalizer_e (D.l1_le hx))
    (fun _ hx => (le_sup_left.trans D.norm_v) (l1_le_l D hx)) C.relIndex_ve C.fpf_e hm hmV

theorem lemma14_7_22 (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    [(V.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)).Normal] :
    ∃ ρ : Γ →* AddMonoid.End
        (Additive (↥(conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⧸
          V.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L))),
      (∀ (l : ↥L) (s : ↥(conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)),
        ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
          Additive.ofMul (QuotientGroup.mk ((secMod_r C D).conjX l s))) ∧
      ((IsoMod ρ ρV ∧ V.relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) =
          4 * V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V)) ∨
        (IsoMod ρ ρCore ∧ V.relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) =
          16 * V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V)) ∨
        (IsoMod ρ ρSt ∧ V.relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) =
          64 * V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V)) ∨
        (IsoMod ρ (prodRep ρV ρSt) ∧
          V.relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) =
            256 * V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V)) ∨
        (IsoMod ρ (prodRep ρCore ρSt) ∧
          V.relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) =
            1024 * V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have SM := secMod_r C D
  obtain ⟨m, hmE, hmV, hmT⟩ := exists_gen_e C D
  have hE₀ := e_eq_closure C D hmE hmV
  have hVR : V ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    C.v_le_e.trans (le_conjClosure _ _)
  have hgen : ∀ s ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L, s ∈ Subgroup.closure
      ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)) := fun s hs =>
    conjClosure_le_closure (l1_le_l D) (le_sup_left.trans D.norm_v) hE₀.le hs
  have hW : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = Subgroup.closure
      ({y | ∃ l : ↥L, θ l ∈ Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)) := by
    apply le_antisymm
    · rw [hE₀, Subgroup.closure_le]
      rintro _ (⟨a, ha, rfl⟩ | hv)
      · refine Subgroup.subset_closure (Or.inl ⟨⟨a, l1_le_l D ha⟩, ?_, rfl⟩)
        exact (D.ll ⟨a, l1_le_l D ha⟩).mpr (D.l1_le ha).2
      · exact Subgroup.subset_closure (Or.inr hv)
    · rw [Subgroup.closure_le]
      rintro _ (⟨l, hl, rfl⟩ | hv)
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_e ⟨l.2, (D.ll l).mp hl⟩) m).mp
          hmE
      · exact C.v_le_e hv
  have hV3 : ¬ 3 ∣ Nat.card V := by rw [D.card_v]; norm_num
  have hcV : ∀ v ∈ V, c * v * c⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp ((le_sup_left.trans D.norm_v) D.c_L) v).mp hv
  have hC : ∀ s, s ∈ cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V ↔
      s ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ∧ c * s * c⁻¹ * s⁻¹ ∈ V := fun s =>
    mem_cfix_sup_iff D.c3 hVR hV3 hcV (r_le_normalizer_v C D) s
  exact SM.h65_cases volI_H_6_5 (le_conjClosure _ L hmE) hmT hgen hW C.relIndex_ve
    (x := ⟨c, D.c_L⟩) D.theta_c3 D.theta_c hC

end CFSG.Quasithin.H13.S4
