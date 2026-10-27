module

public import CFSG.Quasithin.Background.C48SporBlock
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.C48SporS

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem center_kStar_eq_bot {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) :
    Subgroup.center ↥(img (sporN H K) K) = ⊥ := by
  have := isSimpleGroup_kStar hK
  have hperf := commutator_kStar hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(img (sporN H K) K)) with h | h
  · exact h
  · exfalso
    have hcomm : commutator ↥(img (sporN H K) K) = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer, ← h]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x)) y
    obtain ⟨a, b, hab⟩ := (inferInstance : IsSimpleGroup ↥(img (sporN H K) K)).toNontrivial
    apply hab
    have h1 : (⊤ : Subgroup ↥(img (sporN H K) K)) = ⊥ := hperf.symm.trans hcomm
    have ha : a ∈ (⊥ : Subgroup ↥(img (sporN H K) K)) := h1 ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup ↥(img (sporN H K) K)) := h1 ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

@[expose] noncomputable def kStarQuotEquiv {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H) :
    ↥(img (sporN H K) K) ⧸ Subgroup.center ↥(img (sporN H K) K) ≃* ↥K ⧸ Subgroup.center ↥K :=
  (QuotientGroup.quotientMulEquivOfEq (center_kStar_eq_bot hK)).trans
    (QuotientGroup.quotientBot.trans (kStarEquiv (K_le_sporX hK.1)).symm)

@[expose] noncomputable def kEquivKStar {H K : Subgroup G} (hK : CFSG.Open.IsComponentOf K H)
    (hZ : Subgroup.center ↥K = ⊥) : ↥K ≃* ↥(img (sporN H K) K) :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    (kStarEquiv (K_le_sporX hK.1))

theorem isHat_of_mulEquiv {X X' S : Type} [Group X] [Group X'] [Group S] (e : X ≃* X')
    (h : IsHat X S) : IsHat X' S := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hZ : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' := Subgroup.map_center_eq e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ⟨?_⟩⟩
  · rw [← hZ, Subgroup.card_map_of_injective e.injective, hc]
  · exact (QuotientGroup.congr _ _ e hZ).symm.trans f

theorem isExt_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → PV A → PV B)
    (hPY : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → PY A → PY B)
    (h : IsExt X PV PY) : IsExt X' PV PY := by
  obtain ⟨V, hV, hpv, hpy⟩ := h
  have hV' : (V.map e.toMonoidHom).Normal := hV.map _ e.surjective
  exact ⟨V.map e.toMonoidHom, hV', hPV (V.equivMapOfInjective _ e.injective) hpv,
    hPY (QuotientGroup.congr V _ e rfl) hpy⟩

theorem isE2_of_mulEquiv {n : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsE2 n A) :
    IsE2 n B := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem conjClosure_eq_self {Z H : Subgroup G} (hZH : H ≤ Subgroup.normalizer (Z : Set G)) :
    conjClosure Z H = Z := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.2 fun _ ⟨g, hg, z, hz, hx⟩ => hx ▸ ?_
    exact (Subgroup.mem_normalizer_iff.mp (hZH hg) z).mp hz
  · intro z hz
    exact Subgroup.subset_closure ⟨1, H.one_mem, z, hz, by group⟩

section Hyp

variable [Finite G] {H R M L V K : Subgroup G}

theorem imgHom_M0_injective (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hZ : Subgroup.center ↥K = ⊥) :
    Function.Injective (imgHom (N := sporN H K) (M0_le_sporX h h31)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro m hm
  rw [mem_ker_imgHom_iff] at hm
  have hmK : (m : G) ∈ K := h31.1 m.2
  have : (⟨m, hmK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hm g g.2)
  rw [hZ, Subgroup.mem_bot] at this
  have h1 : (m : G) = 1 := congrArg Subtype.val this
  exact (Subgroup.mem_bot).2 (Subtype.ext h1)

theorem isHatA6Block_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hZ : Subgroup.center ↥K = ⊥)
    (hb : IsHatA6Block (img (sporN H K) (conjClosure L M))) : IsHatA6Block (conjClosure L M) := by
  obtain ⟨hS, hhat, hcard, hcent⟩ := hb
  have hUV := blockU_eq_V h h31 hS
  have hL0X := M0_le_sporX h h31
  refine ⟨isShort2_of_img h h31 hS, isHat_of_mulEquiv (modO2EquivL h h31).symm hhat, ?_, ?_⟩
  · have hinj : Function.Injective (blockUHom h h31) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker] at hu
      have hu' : ((⟨u, blockU_le_sporX h h31 u.2⟩ : ↥(sporX H K)) :
          ↥(sporX H K) ⧸ sporN H K) = 1 := by
        rw [← coe_blockUHom h h31 u, hu]
        rfl
      rw [QuotientGroup.eq_one_iff, mem_sporN] at hu'
      have huK : (u : G) ∈ K := h31.1 (blockU_le_M0 _ u.2)
      have : (⟨u, huK⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hu' g g.2)
      rw [hZ, Subgroup.mem_bot] at this
      have h1 : (u : G) = 1 := congrArg Subtype.val this
      exact (Subgroup.mem_bot).2 (Subtype.ext h1)
    rw [← hcard]
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj, blockUHom_surjective h h31⟩)
  · apply le_antisymm
    · rintro x ⟨hxL, hxC⟩
      have hxX := hL0X hxL
      have hmk : ((⟨x, hxX⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ sporN H K) ∈
          img (sporN H K) (conjClosure L M) ⊓ Subgroup.centralizer
            (blockU (img (sporN H K) (conjClosure L M)) : Set (↥(sporX H K) ⧸ sporN H K)) := by
        refine ⟨mk_mem_img hxL, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
        rw [blockU_img h h31] at hb
        obtain ⟨u, hu, rfl⟩ := mem_img.1 hb
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC u hu)
      rw [hcent, ← img_pCoreOf hL0X (isPGroup_ker_M0 h h31)] at hmk
      obtain ⟨o, ho, hox⟩ := mem_img.1 hmk
      have hc := QuotientGroup.eq.mp hox
      rw [mem_sporN] at hc
      have hc' : (o : G)⁻¹ * x ∈ Subgroup.centralizer (K : Set G) := by simpa using hc
      have hoL := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ho
      have h2 := M0_inf_centralizer_le h31
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hoL) hxL, hc'⟩
      have := Subgroup.mul_mem _ ho h2
      simpa using this
    · intro x hx
      refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx, ?_⟩
      rw [hUV]
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hRL : R ≤ Subgroup.normalizer (conjClosure L M : Set G) :=
        h.le_M.trans (le_normalizer_conjClosure L M)
      have hx' := C48Pf.pCoreOf_le_pCoreOf_sup hRL hx
      exact (Subgroup.mem_centralizer_iff.mp (h.V_center hv).2 x hx').symm

theorem c48Case6_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) (hL : L = conjClosure L M) (hZ : Subgroup.center ↥K = ⊥)
    (h6 : C48Case6 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C48Case6 H R M L V K := by
  obtain ⟨hJ4, hS, hcase⟩ := h6
  have hL0X := M0_le_sporX h h31
  have hM0eq : conjClosure (img (sporN H K) (conjClosure L M)) (img (sporN H K) M) =
      img (sporN H K) (conjClosure L M) := by
    rw [← img_conjClosure hL0X (M_le_sporX h h31),
      conjClosure_eq_self (le_normalizer_conjClosure L M)]
  set e : ↥(conjClosure L M) ≃* ↥(img (sporN H K) (conjClosure L M)) :=
    MulEquiv.ofBijective (imgHom hL0X) ⟨imgHom_M0_injective h h31 hZ, imgHom_surjective hL0X⟩
  refine ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hJ4, ?_, ?_⟩
  · rw [hL]
    exact isShort2_of_img h h31 hS
  · rcases hcase with ⟨h24, hext⟩ | ⟨h5, hext⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [hL]
        exact IsSporadic.of_mulEquiv (modO2EquivL h h31).symm h24
      · unfold C31Case6M24 at hext ⊢
        rw [hM0eq] at hext
        exact isExt_of_mulEquiv e.symm (fun f h => isE2_of_mulEquiv f h)
          (fun f h => IsSporadic.of_mulEquiv f h) hext
    · right
      refine ⟨?_, ?_⟩
      · rw [hL]
        exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31).symm h5
      · unfold C31Case6L5 at hext ⊢
        rw [hM0eq] at hext
        exact isExt_of_mulEquiv e.symm (fun f h => isE2_of_mulEquiv f h)
          (fun f h => Setup.Family.statedClassicalModel_of_mulEquiv f h) hext

end Hyp

end CFSG.Quasithin.C48Spor
