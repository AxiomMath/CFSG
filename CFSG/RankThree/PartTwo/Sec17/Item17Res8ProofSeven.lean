module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res5ProofSeven
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def gamma177 (A L : Subgroup G) (c b : G) : Set (Subgroup G) :=
  {Q | Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({b} : Set G)) ∧
    Q = ⁅Q ⊓ Subgroup.centralizer ({c} : Set G), A ⊓ L⁆}

@[expose] noncomputable def n177 (A L : Subgroup G) (c : G) : Subgroup G :=
  sSup {N | ∃ b ∈ A ⊓ L, b ≠ 1 ∧ (N ∈ gamma177 A L c b ∨
    N = CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c))}

end Defs

@[expose] noncomputable def Step177GammaComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      ∀ b ∈ A ⊓ L, b ≠ 1 → ∀ Q ∈ gamma177 A L c b,
        ⁅normalClosureIn (Subgroup.centralizer ({b} : Set G)) c, Q⁆ ≤
          CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c)

@[expose] noncomputable def Step177NRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      inSubgroup perfectResidual (n177 A L c) = Y₀

namespace Proof17Res8

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalClosureIn_mono {K K' : Subgroup G} (h : K ≤ K') (c : G) :
    normalClosureIn K c ≤ normalClosureIn K' c :=
  Subgroup.closure_mono fun _ ⟨m, hm, e⟩ => ⟨m, h hm, e⟩

theorem le_normalizer_n177 {A L : Subgroup G} {c : G}
    (hcomm : ∀ b ∈ A ⊓ L, b ≠ 1 → ∀ Q ∈ gamma177 A L c b,
      ⁅normalClosureIn (Subgroup.centralizer ({b} : Set G)) c, Q⁆ ≤
        CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c)) :
    normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c ≤
      Subgroup.normalizer (n177 A L c : Set G) := by
  set X := normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c with hXdef
  have hXXb : ∀ b ∈ A ⊓ L,
      X ≤ normalClosureIn (Subgroup.centralizer ({b} : Set G)) c := fun b hb =>
    normalClosureIn_mono (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)) c
  have hO2 : ∀ b ∈ A ⊓ L, b ≠ 1 →
      CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c) ≤
        n177 A L c := fun b hb hb1 => le_sSup ⟨b, hb, hb1, Or.inr rfl⟩
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hgen : n177 A L c ≤ (n177 A L c).comap (MulAut.conj x).toMonoidHom := by
    conv_lhs => rw [n177]
    refine sSup_le fun N ⟨b, hb, hb1, hN⟩ => ?_
    intro y hy
    change x * y * x⁻¹ ∈ n177 A L c
    rcases hN with hQ | rfl
    · have hcy : ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2
          (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c) :=
        hcomm b hb hb1 N hQ (Subgroup.commutator_mem_commutator (hXXb b hb hx) hy)
      have hyN : y ∈ n177 A L c := (le_sSup ⟨b, hb, hb1, Or.inl hQ⟩ : N ≤ n177 A L c) hy
      have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (hO2 b hb hb1 hcy) hyN
    · have hxN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
        (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c) (hXXb b hb hx)
      exact hO2 b hb hb1 ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy)
  exact hgen hn

omit [Finite G] in
theorem commutator_commutator_le_of_rotate {N H₁ H₂ H₃ : Subgroup G}
    (h₁ : H₁ ≤ Subgroup.normalizer (N : Set G)) (h₂ : H₂ ≤ Subgroup.normalizer (N : Set G))
    (h₃ : H₃ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  set K := Subgroup.normalizer (N : Set G) with hK
  set f : ↥K →* ↥K ⧸ N.subgroupOf K := QuotientGroup.mk' (N.subgroupOf K) with hf
  have hmap : ∀ {H : Subgroup G}, H ≤ K → (H.subgroupOf K).map K.subtype = H := fun hH => by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hH]
  have key : ∀ X : Subgroup ↥K, X.map K.subtype ≤ N ↔ X.map f = ⊥ := by
    intro X
    rw [Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk', Subgroup.map_le_iff_le_comap]
    rfl
  have e : ∀ {H H' H'' : Subgroup G}, H ≤ K → H' ≤ K → H'' ≤ K →
      ⁅⁅H, H'⁆, H''⁆ =
        (⁅⁅H.subgroupOf K, H'.subgroupOf K⁆, H''.subgroupOf K⁆).map K.subtype := by
    intro H H' H'' hH hH' hH''
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmap hH, hmap hH', hmap hH'']
  rw [e h₂ h₃ h₁, key, Subgroup.map_commutator, Subgroup.map_commutator] at h1
  rw [e h₃ h₁ h₂, key, Subgroup.map_commutator, Subgroup.map_commutator] at h2
  rw [e h₁ h₂ h₃, key, Subgroup.map_commutator, Subgroup.map_commutator]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

omit [Finite G] in
theorem le_normalizer_normalClosureIn' (M : Subgroup G) (c : G) :
    M ≤ Subgroup.normalizer (normalClosureIn M c : Set G) := by
  have key : ∀ m ∈ M, normalClosureIn M c ≤
      (normalClosureIn M c).comap (MulAut.conj m).toMonoidHom := by
    intro m hm
    rw [normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m', hm', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine Subgroup.subset_closure ⟨m * m', M.mul_mem hm hm', ?_⟩
    change m * (m' * c * m'⁻¹) * m⁻¹ = m * m' * c * (m * m')⁻¹
    group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key m hm hx, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) hx
  change m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ ∈ normalClosureIn M c at this
  simpa [mul_assoc] using this

omit [Finite G] in
theorem commutator_le_pCoreOf_two {B Q C : Subgroup G} {c : G} (hBC : B ≤ C) (hQC : Q ≤ C)
    (hQ : Q = ⁅Q ⊓ Subgroup.centralizer ({c} : Set G), B⁆)
    (hXB : ⁅normalClosureIn C c, B⁆ ≤ pPrimeCoreOf 3 (normalClosureIn C c))
    (hperf : normalClosureIn C c ≤ ⁅normalClosureIn C c, normalClosureIn C c⁆ ⊔
      CFSG.Open.pCoreOf 2 (normalClosureIn C c))
    (hcen : ⁅pPrimeCoreOf 3 (normalClosureIn C c), normalClosureIn C c⁆ ≤
      CFSG.Open.pCoreOf 2 (normalClosureIn C c)) :
    ⁅normalClosureIn C c, Q⁆ ≤ CFSG.Open.pCoreOf 2 (normalClosureIn C c) := by
  set X := normalClosureIn C c with hXdef
  set O3 := pPrimeCoreOf 3 X with hO3
  set O2 := CFSG.Open.pCoreOf 2 X with hO2
  set Qc := Q ⊓ Subgroup.centralizer ({c} : Set G) with hQc
  have hCX : C ≤ Subgroup.normalizer (X : Set G) := le_normalizer_normalClosureIn' C c
  have hN3 : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (O3 : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 X
  have hN2 : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (O2 : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hXX : X ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer
  have hQcC : Qc ≤ C := inf_le_left.trans hQC
  have hBX : ⁅B, X⁆ ≤ O3 := by rw [Subgroup.commutator_comm]; exact hXB
  have hstep1 : ⁅⁅Qc, B⁆, X⁆ ≤ O3 := by
    refine commutator_commutator_le_of_rotate ((hQcC.trans hCX).trans hN3)
      ((hBC.trans hCX).trans hN3) (hXX.trans hN3) ?_ ?_
    · exact (Subgroup.commutator_mono hBX le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp ((hQcC.trans hCX).trans hN3))
    · exact (Subgroup.commutator_mono
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQcC.trans hCX)) le_rfl).trans hXB
  have hXQ3 : ⁅X, Q⁆ ≤ O3 := by
    rw [Subgroup.commutator_comm, hQ]
    exact hstep1
  have hstep2 : ⁅⁅X, X⁆, Q⁆ ≤ O2 := by
    refine commutator_commutator_le_of_rotate (hXX.trans hN2) (hXX.trans hN2)
      ((hQC.trans hCX).trans hN2) ?_ ?_
    · exact (Subgroup.commutator_mono hXQ3 le_rfl).trans hcen
    · rw [Subgroup.commutator_comm Q X]
      exact (Subgroup.commutator_mono hXQ3 le_rfl).trans hcen
  have hXXN2 : ⁅X, X⁆ ≤ Subgroup.normalizer (O2 : Set G) :=
    (Subgroup.commutator_le_self X).trans (hXX.trans hN2)
  rw [Subgroup.commutator_le]
  intro x hx q hq
  have hx' : x ∈ ((⁅X, X⁆ ⊔ O2 : Subgroup G) : Set G) := hperf hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXXN2] at hx'
  obtain ⟨h, hh, n, hn, rfl⟩ := hx'
  have hqN : q ∈ Subgroup.normalizer (O2 : Set G) := (hQC.trans hCX).trans hN2 hq
  have hhN : h ∈ Subgroup.normalizer (O2 : Set G) := hXXN2 hh
  have hnq : ⁅n, q⁆ ∈ O2 := by
    have e' : ⁅n, q⁆ = n * (q * n⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e']
    exact mul_mem hn ((Subgroup.mem_normalizer_iff.mp hqN n⁻¹).mp (inv_mem hn))
  have hhq : ⁅h, q⁆ ∈ O2 := hstep2 (Subgroup.commutator_mem_commutator hh hq)
  have e : ⁅h * n, q⁆ = (h * ⁅n, q⁆ * h⁻¹) * ⁅h, q⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp hhN _).mp hnq) hhq

end Proof17Res8

@[expose] noncomputable def Step177XbB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      ∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅normalClosureIn (Subgroup.centralizer ({b} : Set G)) c, A ⊓ L⁆ ≤
          pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c)

@[expose] noncomputable def Step177XbQuasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      (∀ b ∈ A ⊓ L, b ≠ 1 →
        ⁅V, Subgroup.zpowers c⁆ ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) = ⊥) →
      ∀ b ∈ A ⊓ L, b ≠ 1 →
        normalClosureIn (Subgroup.centralizer ({b} : Set G)) c ≤
            ⁅normalClosureIn (Subgroup.centralizer ({b} : Set G)) c,
              normalClosureIn (Subgroup.centralizer ({b} : Set G)) c⁆ ⊔
              CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c) ∧
          ⁅pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c),
              normalClosureIn (Subgroup.centralizer ({b} : Set G)) c⁆ ≤
            CFSG.Open.pCoreOf 2 (normalClosureIn (Subgroup.centralizer ({b} : Set G)) c)

theorem step177GammaComm_of (hB : Step177XbB) (hQ : Step177XbQuasi) : Step177GammaComm := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb b hb hb1 Q hQΓ
  have hA := HeadProof.isE27_of_std hs
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBC : A ⊓ L ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx.1 b hb.1)
  obtain ⟨hperf, hcen⟩ := hQ G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb b hb hb1
  exact Proof17Res8.commutator_le_pCoreOf_two hBC hQΓ.1.2 hQΓ.2
    (hB G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb b hb hb1) hperf hcen

theorem step177MainMB_of (hcomm : Step177GammaComm) (hres : Step177NRes) : Step177MainMB := by
  intro G _ _ A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb
  have hN := Proof17Res8.le_normalizer_n177
    (hcomm G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb)
  have hres' := hres G A c L Y₀ hs h1514 h176 hΩ V hVM hMV hVab hUC hcV hUb
  refine hN.trans ?_
  rw [← hres']
  exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _

theorem step177MainMB_of_parts (hB : Step177XbB) (hQ : Step177XbQuasi) (hres : Step177NRes) :
    Step177MainMB :=
  step177MainMB_of (step177GammaComm_of hB hQ) hres

end CFSG.RankThree.PartTwo.Sec17
