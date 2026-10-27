module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Crd
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Syl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open scoped Matrix

namespace Sec1211Ns

theorem isSylowTwoOf_of_inf_normalizer_le {G : Type} [Group G] [Finite G] {K S M : Subgroup G}
    (hSK : S ≤ K) (hNM : K ⊓ Subgroup.normalizer (S : Set G) ≤ M)
    (hSyl : IsSylowTwoOf S (K ⊓ M)) : IsSylowTwoOf S K := by
  rw [A4.isSylowTwoOf_iff_maximal] at hSyl ⊢
  refine ⟨hSK, hSyl.2.1, fun P hPK hP hSP => ?_⟩
  have h1 : P ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
    hSyl.2.2 _ (le_inf (inf_le_left.trans hPK)
      ((inf_le_inf_right _ hPK).trans hNM)) (hP.to_le inf_le_left)
      (le_inf hSP Subgroup.le_normalizer)
  by_contra hne
  have hlt : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxnot (Subgroup.mem_subgroupOf.mpr (h1 ⟨x.2, hxNorm⟩))

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ} (F : Frame S m)

theorem psi_eq_one_iff_gen {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) (a : ↥Y) :
    psi F hY a = 1 ↔ (a : G) ∈ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) := by
  constructor
  · intro h1
    have h1' : frameMat F (psi F hY a) = 1 := by
      rw [h1]
      simp [frameMat]
    have hle : S.W₁ ⊔ S.W₂ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := psi_spec₁ F hY a hx.1
        rw [h1', Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h2
        exact ((conj_eq_iff₁ (hY a.2).1.2 hx.1 (g := 1)
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]; exact h2)).mpr
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec])).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := psi_spec₂ F hY a hy.1
        rw [h1', map_one, Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h2
        exact ((conj_eq_iff₂ (S.Xv_le_normalizer₂ (hY a.2)) hy.1 (g := 1)
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]; exact h2)).mpr
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec])).symm
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  · intro h
    refine PairStab.eq_of_mulVec_eq fun ξ => ?_
    rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    have hx : S.C₁.inv ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h ξ) ∈ S.W₁ :=
      ⟨S.C₁.inv_mem _, by
        show S.C₁.E (S.C₁.inv _) ⬝ᵥ S.C₂.E c₀ = 0
        rw [S.C₁.E_inv]
        exact s_emb_dot F _⟩
    have h1 := psi_spec₁ F hY a hx.1
    have h2 := (conj_eq_iff₁ (hY a.2).1.2 hx.1 h1).mp
      (Subgroup.mem_centralizer_iff.mp h _ (Subgroup.mem_sup_left hx)).symm
    rw [S.C₁.E_inv, frameMat_mulVec_emb] at h2
    have h3 := congrArg (fun z => ((F.s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h2
    simp only [VecStab.inv_mulVec_mulVec] at h3
    exact PairStab.emb_injective F.h h3

theorem mem_ker_psi_of_mem_pCoreOf (hm : 3 ≤ m) {u : G}
    (hu : u ∈ pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) (hul : u ∈ Sec1216Lv.lv L (a₀ * c₀)) :
    psi F S.lv_le_Xv ⟨u, hul⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (CFSG.pCore 2 ↥(Sec1216Lv.lv L (a₀ * c₀))).map (psi F S.lv_le_Xv) with hP
  have hPn : P.Normal := Subgroup.Normal.map CFSG.pCore_normal _ (psi_lv_surjective F)
  have hP2 : IsPGroup 2 P := (CFSG.pCore_isPGroup).map _
  have hPb := KGH91.NatCoord.eq_bot_of_normal_isPGroup hm hP2
  obtain ⟨u', hu', hu'u⟩ := hu
  have h1 : psi F S.lv_le_Xv u' ∈ P := ⟨u', by exact hu', rfl⟩
  rw [hPb, Subgroup.mem_bot] at h1
  have : u' = ⟨u, hul⟩ := Subtype.ext hu'u
  rw [← this]
  exact h1

theorem mem_centralizer_W_of_mem_pCoreOf (F : Frame S m) (hm : 3 ≤ m) {u : G}
    (hu : u ∈ pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) :
    u ∈ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) := by
  have hul : u ∈ Sec1216Lv.lv L (a₀ * c₀) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hu
  exact (psi_eq_one_iff_gen F S.lv_le_Xv ⟨u, hul⟩).mp (mem_ker_psi_of_mem_pCoreOf F hm hu hul)

theorem exists_ne_one_W₁ (F : Frame S m) (hm : 1 ≤ m) : ∃ a ∈ S.W₁, a ≠ 1 := by
  set C := natCoord₁ F
  refine ⟨C.inv (Pi.single ⟨0, by omega⟩ 1), C.inv_mem _, fun h => ?_⟩
  have h1 := C.E_inv (Pi.single ⟨0, by omega⟩ 1)
  rw [h, C.E_one] at h1
  have h2 := congrFun h1 ⟨0, by omega⟩
  simp at h2

theorem mem_centralizer_V_of_mem_section (F : Frame S m) (hm : 3 ≤ m) {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G))
    (hxv : x ∈ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (hxs : x ∈ centralizerSection ⊤ (Sec1216Lv.lv L (a₀ * c₀))
      (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨-, hxN, -, hxc⟩ := hxs
  have hu : ∀ l ∈ Sec1216Lv.lv L (a₀ * c₀),
      x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)) := fun l hl => by
    have h1 := Subgroup.inv_mem _ (hxc l hl)
    have e : (l * x * l⁻¹ * x⁻¹)⁻¹ = x * l * x⁻¹ * l⁻¹ := by group
    rwa [e] at h1
  have hxl : ∀ l ∈ Sec1216Lv.lv L (a₀ * c₀),
      x * l * x⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
  by_cases hx1 : x ∈ Subgroup.normalizer (V₁ : Set G)
  ·
    have hX : x ∈ Xv L V₁ (a₀ * c₀) := ⟨⟨hxM, hx1⟩, hxv⟩
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
      Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hm
    have hcen : theta F ⟨x, hX⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨⟨l, hl⟩, rfl⟩ := psi_lv_surjective F g
      have hlX : l ∈ Xv L V₁ (a₀ * c₀) := S.lv_le_Xv hl
      have hxlX : x * l * x⁻¹ ∈ Xv L V₁ (a₀ * c₀) := S.lv_le_Xv (hxl l hl)
      have hul : x * l * x⁻¹ * l⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) :=
        (Sec1216Lv.lv L _).mul_mem (hxl l hl) ((Sec1216Lv.lv L _).inv_mem hl)
      have h1 := mem_ker_psi_of_mem_pCoreOf F hm (hu l hl) hul
      have h2 : theta F ⟨x * l * x⁻¹ * l⁻¹, S.lv_le_Xv hul⟩ = 1 := h1
      have e : (⟨x * l * x⁻¹ * l⁻¹, S.lv_le_Xv hul⟩ : ↥(Xv L V₁ (a₀ * c₀))) =
          ⟨x, hX⟩ * ⟨l, hlX⟩ * ⟨x, hX⟩⁻¹ * ⟨l, hlX⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      have h3 : theta F ⟨x, hX⟩ * theta F ⟨l, hlX⟩ = theta F ⟨l, hlX⟩ * theta F ⟨x, hX⟩ := by
        calc theta F ⟨x, hX⟩ * theta F ⟨l, hlX⟩ =
            theta F ⟨x, hX⟩ * theta F ⟨l, hlX⟩ * (theta F ⟨x, hX⟩)⁻¹ *
              (theta F ⟨l, hlX⟩)⁻¹ * (theta F ⟨l, hlX⟩ * theta F ⟨x, hX⟩) := by group
          _ = theta F ⟨l, hlX⟩ * theta F ⟨x, hX⟩ := by rw [h2, one_mul]
      exact h3.symm
    have hnab : ∃ a b : Matrix.SpecialLinearGroup (Fin m) (ZMod 2), a * b ≠ b * a :=
      Sec121Thm.exists_not_commute_SL hm
    have hcb : Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2))) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    rw [hcb, Subgroup.mem_bot] at hcen
    have hf1 : frameMat F (theta F ⟨x, hX⟩) = 1 := by rw [hcen]; simp [frameMat]
    have hfix₁ : ∀ a ∈ V₁, x * a * x⁻¹ = a := fun a ha => by
      have h1 := theta_spec₁ F ⟨x, hX⟩ ha
      rw [hf1, Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h1
      exact S.C₁.inj _ ((Subgroup.mem_normalizer_iff.mp hx1 a).mp ha) a ha h1
    have hfix₂ : ∀ c ∈ V₂, x * c * x⁻¹ = c := fun c hc => by
      have h1 := theta_spec₂ F ⟨x, hX⟩ hc
      rw [hf1, map_one, Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h1
      exact S.C₂.inj _ ((Subgroup.mem_normalizer_iff.mp (S.Xv_le_normalizer₂ hX) c).mp hc) c hc h1
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hy
    have h3 : x * (a * c) * x⁻¹ = a * c := by
      calc x * (a * c) * x⁻¹ = (x * a * x⁻¹) * (x * c * x⁻¹) := by group
        _ = a * c := by rw [hfix₁ a ha, hfix₂ c hc]
    calc a * c * x = x * (a * c) * x⁻¹ * x := by rw [h3]
      _ = x * (a * c) := by group
  ·
    exfalso
    rcases S.fix_or_swap hxM with ⟨h₁, -⟩ | ⟨hs₁, hs₂⟩
    · exact hx1 h₁
    have hxa : x * a₀ * x⁻¹ ∈ V₂ := (hs₁ a₀).1 S.ha₀
    have hxc : x * c₀ * x⁻¹ ∈ V₁ := (hs₂ c₀).1 S.hc₀
    have hv := Subgroup.mem_centralizer_singleton_iff.mp hxv
    have e : x * c₀ * x⁻¹ * (x * a₀ * x⁻¹) = a₀ * c₀ := by
      calc x * c₀ * x⁻¹ * (x * a₀ * x⁻¹) = x * (c₀ * a₀) * x⁻¹ := by group
        _ = x * (a₀ * c₀) * x⁻¹ := by rw [S.comm (S.le₂ S.hc₀) (S.le₁ S.ha₀)]
        _ = a₀ * c₀ := by rw [hv, mul_inv_cancel_right]
    have htc : x * c₀ * x⁻¹ = a₀ := (S.decomp_unique hxc S.ha₀ hxa S.hc₀ e).1
    obtain ⟨a, ha, ha1⟩ := exists_ne_one_W₁ F (by omega)
    apply ha1
    have hfa := (natCoord₁ F).eq_one_of_dual hm (C' := natCoord₂ F) (natCoord₂_ρ F)
      (f := fun w => x * w * x⁻¹) (fun w hw => conj_mem_W₂ hxM htc hs₁ hs₂ hw)
      (fun a _ b _ => by group) (fun l w hw => ?_) a ha
    · calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = 1 := by rw [hfa]; group
    ·
      have hl := l.2
      have hwW := S.lv_conj_mem_W₁ hl hw
      have hW₂ : x * ((l : G) * w * (l : G)⁻¹) * x⁻¹ ∈ S.W₂ := conj_mem_W₂ hxM htc hs₁ hs₂ hwW
      have hxw : x * w * x⁻¹ ∈ S.W₂ := conj_mem_W₂ hxM htc hs₁ hs₂ hw
      have hlxw : (l : G) * (x * w * x⁻¹) * (l : G)⁻¹ ∈ S.W₂ := S.lv_conj_mem_W₂ hl hxw
      have huC := mem_centralizer_W_of_mem_pCoreOf F hm (hu l hl)
      have h1 := Subgroup.mem_centralizer_iff.mp huC _
        (Subgroup.mem_sup_right hlxw)
      show x * ((l : G) * w * (l : G)⁻¹) * x⁻¹ = (l : G) * (x * w * x⁻¹) * (l : G)⁻¹
      calc x * ((l : G) * w * (l : G)⁻¹) * x⁻¹ =
          (x * l * x⁻¹ * (l : G)⁻¹) * ((l : G) * (x * w * x⁻¹) * (l : G)⁻¹) *
            (x * l * x⁻¹ * (l : G)⁻¹)⁻¹ := by group
        _ = (l : G) * (x * w * x⁻¹) * (l : G)⁻¹ := by
          rw [← h1]
          group

theorem mem_pCoreOf_of_mem_centralizer_W (F : Frame S m) {u : G}
    (hul : u ∈ Sec1216Lv.lv L (a₀ * c₀))
    (huW : u ∈ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)) :
    u ∈ pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (psi F S.lv_le_Xv).ker.map (Sec1216Lv.lv L (a₀ * c₀)).subtype with hK
  have hKle : K ≤ Sec1216Lv.lv L (a₀ * c₀) := Subgroup.map_subtype_le _
  have hKn : Sec1216Lv.lv L (a₀ * c₀) ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    refine Sec121Swap.mem_normalizer_of_conj_mem fun k hk => ?_
    obtain ⟨k', hk', rfl⟩ := hk
    refine ⟨⟨l, hl⟩ * k' * ⟨l, hl⟩⁻¹, ?_, rfl⟩
    have hk1 : psi F S.lv_le_Xv k' = 1 := hk'
    show psi F S.lv_le_Xv (⟨l, hl⟩ * k' * ⟨l, hl⟩⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hk1, mul_one, mul_inv_cancel]
  have hK2 : IsPGroup 2 K := (isPGroup_ker_psi_lv F).map _
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKle hKn hK2 ⟨⟨u, hul⟩, ?_, rfl⟩
  exact (psi_eq_one_iff_gen F S.lv_le_Xv ⟨u, hul⟩).mpr huW

theorem mem_normalizer_centralizerSection {H : Subgroup G} {g : G} (hgH : g ∈ H)
    (hgN : g ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G)) :
    g ∈ Subgroup.normalizer ((centralizerSection H (Sec1216Lv.lv L (a₀ * c₀))
      (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) : Subgroup G) : Set G) := by
  have hgO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hgN
  refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨hyH, hyN, hyO, hyc⟩ := hy
  refine ⟨H.mul_mem (H.mul_mem hgH hyH) (H.inv_mem hgH),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hyN) (Subgroup.inv_mem _ hgN),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgO hyO) (Subgroup.inv_mem _ hgO), fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ Sec1216Lv.lv L (a₀ * c₀) := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) l).mp hl
    rwa [inv_inv] at this
  have h1 := hyc _ hl'
  have h2 := (Subgroup.mem_normalizer_iff.mp hgO _).mp h1
  have e : g * (g⁻¹ * l * g * y * (g⁻¹ * l * g)⁻¹ * y⁻¹) * g⁻¹ =
      l * (g * y * g⁻¹) * l⁻¹ * (g * y * g⁻¹)⁻¹ := by group
  rwa [e] at h2

theorem exists_sylow_of_normal (h331 : Stmt3_3_1) (F : Frame S m) (hm : 3 ≤ m)
    (hnorm : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤
      Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G)) :
    ∃ R : Subgroup G, IsSylowTwoOf R (Subgroup.centralizer ({a₀ * c₀} : Set G)) ∧
      R ≤ Subgroup.normalizer (L : Set G) ∧ T ⊓ Subgroup.centralizer (V : Set G) ≤ R ∧
        R ⊓ centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
          (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) =
          T ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.hVe.1
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  set Mv := M ⊓ H with hMv
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLv
  set Ys := centralizerSection H Lv (pCoreOf 2 Lv) with hYs
  have hCV : Subgroup.centralizer (V : Set G) ≤ H := Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr S.v_mem)
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hQMv : Q ≤ Mv := le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hRM : R ≤ M := hR.1.trans inf_le_left
  have hRH : R ≤ H := hR.1.trans inf_le_right
  have hTM : IsSylowTwoOf T M := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow S.hTL
  have hQsyl : IsSylowTwoOf (T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)))
      (M ⊓ Subgroup.centralizer (V : Set G)) :=
    A4.isSylowTwoOf_inf_normal hTM inf_le_left fun m hm =>
      Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer hm)
        (normalizer_le_normalizer_centralizer V (S.le_normalizer hm))
  have hQeq : T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) = Q := by
    rw [hQ, ← inf_assoc, inf_eq_left.mpr S.hTL]
  rw [hQeq] at hQsyl
  have hRQ : R ⊓ Subgroup.centralizer (V : Set G) ≤ Q :=
    (A4.isSylowTwoOf_iff_maximal.mp hQsyl).2.2 _ (inf_le_inf_right _ hRM)
      (hR.2.1.to_le inf_le_left) (le_inf hQR inf_le_right)
  have hQLv : Q ≤ Subgroup.normalizer (Lv : Set G) :=
    Sec1216Lv.le_normalizer_lv (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  have hRYs : R ⊓ Ys = Q := by
    refine le_antisymm (fun x hx => hRQ ⟨hx.1, ?_⟩) (le_inf hQR fun q hq => ?_)
    · obtain ⟨-, hxN, hxO, hxc⟩ := hx.2
      exact mem_centralizer_V_of_mem_section F hm (hRM hx.1) (hRH hx.1)
        ⟨Subgroup.mem_top x, hxN, hxO, hxc⟩
    · have hqN := hQLv hq
      refine ⟨hCV hq.2, hqN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hqN,
        fun l hl => ?_⟩
      have hql : q * l⁻¹ * q⁻¹ ∈ Lv :=
        (Subgroup.mem_normalizer_iff.mp hqN _).mp (Lv.inv_mem hl)
      have hmem : l * q * l⁻¹ * q⁻¹ ∈ Lv := by
        have e : l * q * l⁻¹ * q⁻¹ = l * (q * l⁻¹ * q⁻¹) := by group
        rw [e]
        exact Lv.mul_mem hl hql
      refine mem_pCoreOf_of_mem_centralizer_W F hmem ?_
      have hlV : l ∈ Subgroup.normalizer (V : Set G) :=
        S.le_normalizer (Subgroup.le_normalizer (Sec1216Lv.lv_le_L L _ hl))
      have hqC : q ∈ Subgroup.centralizer (V : Set G) := hq.2
      have hlqC : l * q * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer V hlV) q).mp hqC
      have hc : l * q * l⁻¹ * q⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.mul_mem _ hlqC (Subgroup.inv_mem _ hqC)
      exact Subgroup.centralizer_le (by exact_mod_cast S.W_le_V) hc
  have huniq := Sec1215.isUniqueM_of_hyp121 h331 S.hyp S.hTL
  have hNR : H ⊓ Subgroup.normalizer (R : Set G) ≤ M := by
    rintro g ⟨hgH, hgR⟩
    have hgN := hnorm hgH
    have hgYs := mem_normalizer_centralizerSection (H := H) hgH hgN
    have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := by
      rw [← hRYs]
      exact Sec1216Gen.mem_normalizer_inf hgR hgYs
    exact huniq.1.2 hgQ
  refine ⟨R, isSylowTwoOf_of_inf_normalizer_le hRH hNR (by rw [inf_comm]; exact hR), hRM, hQR,
    hRYs⟩

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
