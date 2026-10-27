module

public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem520

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

theorem inf_pCoreOf_oTwoUpper_le (H : Subgroup G) :
    pCoreOf 2 H ⊓ oTwoUpper H ≤ pCoreOf 2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  exact le_normalizer_inf ((oTwoUpper_le H).trans (le_normalizer_pCoreOf 2 H))
    Subgroup.le_normalizer

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h


theorem le_pCoreOf_of_not_le
    {N : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hnot : ¬ oTwoUpper H ≤ N) :
    N ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hKH : K ≤ H := oTwoUpper_le H
  have hNK : N ⊓ K ≤ pCoreOf 2 K := by
    have hsimp := h.isSimple_K
    have hNKn : ((N ⊓ K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        (le_normalizer_inf (hKH.trans hHN) Subgroup.le_normalizer)
    rcases hsimp.eq_bot_or_eq_top_of_normal (((N ⊓ K).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
      intro x hx
      have hxN : (⟨x, hx.2⟩ : ↥K) ∈ (N ⊓ K).subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have hxP : (⟨x, hx.2⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
        exact hb hxN
      exact ⟨_, hxP, rfl⟩
    · exfalso
      apply hnot
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyH, hyo⟩
      have hyK : y ∈ K := mem_oTwoUpper_of_odd hyH hyo
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨y, hyK⟩ ∈
          ((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        rw [ht]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hcy⟩ := hmem
      have ho' : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (c⁻¹ * ⟨y, hyK⟩) = 1 := by
        rw [map_mul, map_inv, hcy, inv_mul_cancel]
      have ho : c⁻¹ * ⟨y, hyK⟩ ∈ CFSG.pCore 2 ↥K := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, ho⟩
      have hk' : (c⁻¹ * ⟨y, hyK⟩) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hσc : (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) c = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hc
      have hσy : (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) ⟨y, hyK⟩ =
          (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) (c⁻¹ * ⟨y, hyK⟩) := by
        rw [map_mul, map_inv, hσc, inv_one, one_mul]
      have hpow : (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) ((⟨y, hyK⟩ : ↥K) ^ 2 ^ k) = 1 := by
        rw [map_pow, hσy, ← map_pow, hk', map_one]
      have hmemN : (⟨y, hyK⟩ : ↥K) ^ 2 ^ k ∈ (N ⊓ K).subgroupOf K := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hpow
      rw [Subgroup.mem_subgroupOf] at hmemN
      have hyk : y ^ 2 ^ k ∈ N := by simpa using hmemN.1
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
        (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hyo) : Nat.Coprime (2 ^ k) (orderOf y))
      rw [← hm]
      exact N.pow_mem hyk m
  have hNCK : N ≤ H ⊓ centralizerModO2 K := by
    intro x hx
    refine ⟨hNH hx, hKN (hNH hx), normalizer_le_normalizer_pCoreOf 2 K (hKN (hNH hx)),
      fun u hu => hNK ⟨?_, ?_⟩⟩
    · have h1 : u * x⁻¹ * u⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hHN (hKH hu)) x⁻¹).mp (N.inv_mem hx)
      have := N.mul_mem hx h1
      simpa [mul_assoc] using this
    · have h1 : x * u * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKN (hNH hx)) u).mp hu
      exact K.mul_mem h1 (K.inv_mem hu)
  exact hNCK.trans h.inf_centralizerModO2_le

end Hyp5_1_14

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem H_le_normalizer_Z₁ (h5114 : Stmt5_1_14_first) :
    H ≤ Subgroup.normalizer (Z₁ : Set G) :=
  (s.H_le_centralizer h5114).trans (Subgroup.centralizer_le_normalizer _)

theorem Z₁_le_T : Z₁ ≤ T := s.Z₁_le_Z.trans (quasithinOmegaOneCenter_le_self T)

theorem not_le_centralizer_V₂ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    ¬ oTwoUpper H ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
  intro hKC
  apply s.not_le
  have hHN : H ≤ Subgroup.normalizer (conjClosure Z₁ D₃ : Set G) := by
    rw [s.hyp.H_eq_sup]
    exact sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _)) (s.T_le_normalizer_V₂ hF)
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hV₂ne : conjClosure Z₁ D₃ ≠ ⊥ := fun hb' => hz1 (by
    have := (le_conjClosure Z₁ D₃) hz
    rw [hb'] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (conjClosure Z₁ D₃ : Set G)) :=
    ⟨conjClosure Z₁ D₃, hV₂ne, isPGroup_of_isElemAbelian s.isElemAbelian_V₂, rfl⟩
  obtain ⟨M', hM', hle'⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := (s.hyp.isUniqueM h5114).2 M' ⟨hM', hHN.trans hle'⟩
  exact (le_normalizer_conjClosure Z₁ D₃).trans (hM'eq ▸ hle')

theorem not_tildeOf_K_le_centralizer (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) : Set (SecQuot
        (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  intro hKC
  apply s.not_le_centralizer_V₂ h5114 hF
  have hHN := s.H_le_normalizer_Z₁ h5114
  have hHC := s.H_le_centralizer h5114
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have hV₂H : conjClosure Z₁ D₃ ≤ conjClosure (conjClosure Z₁ D₃) H := le_conjClosure _ H
  have hV₂N : conjClosure Z₁ D₃ ≤ Subgroup.normalizer (Z₁ : Set G) :=
    (s.V₂_le_T.trans s.hyp.hyp.hStar.1.1).trans hHN
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyH, hyo⟩
  have hyK : y ∈ oTwoUpper H := mem_oTwoUpper_of_odd hyH hyo
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro v hv
  have hc : y * v * y⁻¹ * v⁻¹ ∈ Z₁ := by
    have h1 := Subgroup.mem_centralizer_iff.mp
      (hKC (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨y, hHN hyH⟩) hyK)) _
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (x := ⟨v, hV₂N hv⟩)
        (hV₂H hv))
    have := commutator_mem_of_secMk_commute h1.symm
    simpa using this
  have hyz : y * z = z * y := (Subgroup.mem_centralizer_iff.mp (hHC hyH) z hz).symm
  rcases s.eq_one_or_eq hz hz1 hc with h1 | h1
  · have : y * v * y⁻¹ = v := by
      have := congrArg (· * v) h1
      simpa using this
    have e : y * v = v * y := by
      have := congrArg (· * y) this
      simpa [mul_assoc] using this
    exact e.symm
  · exfalso
    have e : y * v * y⁻¹ = z * v := by
      rw [← h1]; group
    exact conj_ne_mul_of_odd hyz hz2 hz1 hyo e

theorem tildeOf_pCoreOf_le_centralizer (h5114 : Stmt5_1_14_first) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    tildeOf Z₁ (pCoreOf 2 H) ≤ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) : Set (SecQuot
        (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  have h21 := (h521 G T M L V H B D D₃ Z₁ H n s.hyp.hyp s.hyp.notation59 s.hyp.module
    s.hyp.l34 hnot s.le_D s.card_D₃ s.z1 le_rfl (s.H_le_centralizer h5114)).1
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
  have hc : (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ ∈ Z₁ :=
    h21 (Subgroup.commutator_mem_commutator hu hx)
  have h1 : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (u * x * u⁻¹ * x⁻¹) = 1 := by
    rw [secMk_eq_one_iff]; simpa using hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ x) h1
  simp only [one_mul, inv_mul_cancel_right] at this
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ u) this
  simpa [mul_assoc] using this

end Setup521

section Kernel

variable {Z₁ : Subgroup G}

omit [Finite G] in
theorem tildeOf_mono {X Y : Subgroup G} (h : X ≤ Y) : tildeOf Z₁ X ≤ tildeOf Z₁ Y :=
  secImg_mono h

@[expose] def tildeCent (Z₁ X : Subgroup G)
    (W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) : Subgroup G :=
  X ⊓ ((Subgroup.centralizer (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))).comap
    (tmk Z₁)).map (Subgroup.normalizer (Z₁ : Set G)).subtype

omit [Finite G] in
theorem mem_tildeCent_iff {X : Subgroup G}
    {W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)} {x : G}
    (hxN : x ∈ Subgroup.normalizer (Z₁ : Set G)) :
    x ∈ tildeCent Z₁ X W ↔ x ∈ X ∧
      tmk Z₁ ⟨x, hxN⟩ ∈ Subgroup.centralizer
        (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  constructor
  · rintro ⟨hxX, y, hy, hyx⟩
    have : y = ⟨x, hxN⟩ := Subtype.ext hyx
    exact ⟨hxX, this ▸ hy⟩
  · rintro ⟨hxX, hx⟩
    exact ⟨hxX, ⟨x, hxN⟩, hx, rfl⟩

@[expose] noncomputable def tildeRes (Z₁ X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (Z₁ : Set G)) : ↥X →* ↥(tildeOf Z₁ X) :=
  ((tmk Z₁).comp (Subgroup.inclusion hX)).codRestrict (tildeOf Z₁ X)
    (fun x => secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
      (x := Subgroup.inclusion hX x) x.2)

omit [Finite G] in
theorem tildeRes_apply {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (Z₁ : Set G)) (x : ↥X) :
    ((tildeRes Z₁ X hX x : ↥(tildeOf Z₁ X)) : SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁) =
      tmk Z₁ ⟨x, hX x.2⟩ := rfl

omit [Finite G] in
theorem tildeRes_surjective {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (Z₁ : Set G)) :
    Function.Surjective (tildeRes Z₁ X hX) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

@[expose] noncomputable def tildeAct (Z₁ X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (Z₁ : Set G))
    (W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) :
    ↥X →* ↥(autOn (tildeOf Z₁ X) W) :=
  (InternalSec.autOnHom hXW).comp (tildeRes Z₁ X hX)

omit [Finite G] in
theorem tildeAct_surjective {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (Z₁ : Set G))
    {W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)}
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) :
    Function.Surjective (tildeAct Z₁ X hX W hXW) :=
  (InternalSec.autOnHom_surjective _).comp (tildeRes_surjective _)

omit [Finite G] in
theorem mem_ker_tildeAct {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (Z₁ : Set G))
    {W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)}
    (hXW : tildeOf Z₁ X ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) (x : ↥X) :
    x ∈ (tildeAct Z₁ X hX W hXW).ker ↔
      tmk Z₁ ⟨x, hX x.2⟩ ∈ Subgroup.centralizer
        (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  unfold tildeAct
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    InternalSec.mem_ker_autOnHom]
  rfl

end Kernel

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

section Section

variable {W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)}

theorem tildeCent_le_pCoreOf
    (h5114 : Stmt5_1_14_first)
    (hW : tildeOf Z₁ H ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hKW : ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) :
    tildeCent Z₁ H W ≤ pCoreOf 2 H := by
  have hHN := s.H_le_normalizer_Z₁ h5114
  have hnorm : H ≤ Subgroup.normalizer (tildeCent Z₁ H W : Set G) := by
    intro h hh
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hxH : x ∈ H := hx.1
    have hy : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    refine (mem_tildeCent_iff (hHN hy)).mpr ⟨hy, ?_⟩
    have hx' := ((mem_tildeCent_iff (hHN hxH)).mp hx).2
    have hπh := le_normalizer_centralizer_of_le_normalizer hW
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨h, hHN hh⟩) hh)
    have h1 := (Subgroup.mem_normalizer_iff.mp hπh _).mp hx'
    have e : (⟨h * x * h⁻¹, hHN hy⟩ : ↥(Subgroup.normalizer (Z₁ : Set G))) =
        ⟨h, hHN hh⟩ * ⟨x, hHN hxH⟩ * ⟨h, hHN hh⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact h1
  refine s.hyp.le_pCoreOf_of_not_le inf_le_left hnorm fun hK => hKW ?_
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  exact ((mem_tildeCent_iff x.2).mp (hK hx)).2

theorem mem_pCoreOf_of_mem_centralizer
    (h5114 : Stmt5_1_14_first)
    (hW : tildeOf Z₁ H ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hKW : ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    {h : G} (hh : h ∈ H) (hN : h ∈ Subgroup.normalizer (Z₁ : Set G))
    (hc : tmk Z₁ ⟨h, hN⟩ ∈
      Subgroup.centralizer (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) :
    h ∈ pCoreOf 2 H :=
  s.tildeCent_le_pCoreOf h5114 hW hKW ((mem_tildeCent_iff hN).mpr ⟨hh, hc⟩)

omit s in
theorem pCoreOf_K_le : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (oTwoUpper_le H))
    ((le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

variable (hWU : W ≤ tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H))
  (hW : tildeOf Z₁ H ≤ Subgroup.normalizer
    (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
  (hKW : ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
    (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
include hWU hW hKW

theorem ker_tildeAct_K
    (h5114 : Stmt5_1_14_first) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    (tildeAct Z₁ (oTwoUpper H) ((oTwoUpper_le H).trans (s.H_le_normalizer_Z₁ h5114)) W
      ((tildeOf_mono (oTwoUpper_le H)).trans hW)).ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext k
  rw [mem_ker_tildeAct]
  constructor
  · intro hc
    have h2 := s.mem_pCoreOf_of_mem_centralizer h5114 hW hKW (oTwoUpper_le H k.2) _ hc
    obtain ⟨k', hk', hk'k⟩ := inf_pCoreOf_oTwoUpper_le H ⟨h2, k.2⟩
    have : k' = k := Subtype.ext hk'k
    rw [← this]
    exact hk'
  · intro hk
    have h1 : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := ⟨k, by assumption, rfl⟩
    have h2 := s.tildeOf_pCoreOf_le_centralizer h5114 h521 hnot
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨k, s.H_le_normalizer_Z₁ h5114 (oTwoUpper_le H k.2)⟩) (pCoreOf_K_le h1))
    exact Subgroup.centralizer_le hWU h2

theorem lieModel_autOn
    (h5114 : Stmt5_1_14_first) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    LieModel ↥(autOn (tildeOf Z₁ (oTwoUpper H)) W) .PSL 3 2 2 := by
  have hker := s.ker_tildeAct_K hWU hW hKW h5114 h521 hnot
  let e : O2Q (oTwoUpper H) ≃* ↥(autOn (tildeOf Z₁ (oTwoUpper H)) W) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (tildeAct_surjective _ _))
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e s.hyp.l34

theorem isPGroup_inf_centralizer
    (h5114 : Stmt5_1_14_first) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    IsPGroup 2 ↥(tildeOf Z₁ (oTwoUpper H) ⊓ Subgroup.centralizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := s.ker_tildeAct_K hWU hW hKW h5114 h521 hnot
  rintro ⟨x, hxK, hxC⟩
  obtain ⟨k, hk, rfl⟩ := mem_secImg.mp hxK
  have hk' : (⟨k, hk⟩ : ↥(oTwoUpper H)) ∈ CFSG.pCore 2 ↥(oTwoUpper H) := by
    rw [← hker, mem_ker_tildeAct]
    exact hxC
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, hk'⟩
  have ha' : (k : G) ^ 2 ^ a = 1 := by
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥(oTwoUpper H)) => ((y : ↥(oTwoUpper H)) : G)) ha
    simpa using this
  have hka : k ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha')
  refine ⟨a, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, hka, map_one]

theorem pCoreOf_autOn_eq_bot
    (h5114 : Stmt5_1_14_first) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    pCoreOf 2 (autOn (tildeOf Z₁ H) W) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN := s.H_le_normalizer_Z₁ h5114
  set ρ := tildeAct Z₁ H hHN W hW with hρ
  have hsurj : Function.Surjective ρ := tildeAct_surjective _ _
  have hkerρ : ∀ x : ↥H, x ∈ ρ.ker → (x : G) ∈ pCoreOf 2 H := fun x hx =>
    s.mem_pCoreOf_of_mem_centralizer h5114 hW hKW x.2 _ ((mem_ker_tildeAct _ _ x).mp hx)
  have hρO : ∀ y : ↥H, (y : G) ∈ pCoreOf 2 H → ρ y = 1 := by
    intro y hy
    rw [← MonoidHom.mem_ker, mem_ker_tildeAct]
    exact Subgroup.centralizer_le hWU (s.tildeOf_pCoreOf_le_centralizer h5114 h521 hnot
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨y, hHN y.2⟩) hy))
  set Q := CFSG.Open.pCore 2 ↥(autOn (tildeOf Z₁ H) W) with hQ
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQp : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hPre2 : IsPGroup 2 ↥((Q.comap ρ).map H.subtype) := by
    rintro ⟨x, ⟨y, hy, rfl⟩⟩
    obtain ⟨a, ha⟩ := hQp ⟨ρ y, Subgroup.mem_comap.mp hy⟩
    have h1 : ρ (y ^ 2 ^ a) = 1 := by
      rw [map_pow]; simpa using congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hkerρ _ h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((y : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.subtype_apply]
    rw [pow_add, pow_mul, hb']
  have hPreN : H ≤ Subgroup.normalizer (((Q.comap ρ).map H.subtype : Subgroup G) : Set G) := by
    intro h hh
    apply mem_normalizer_of_forall_conj_mem'
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact hQn.conj_mem _ (Subgroup.mem_comap.mp hy) _
  have hPreO : (Q.comap ρ).map H.subtype ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hPreN hPre2
  have hQbot : Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := hsurj q
    rw [Subgroup.mem_bot]
    exact hρO y (hPreO ⟨y, Subgroup.mem_comap.mpr hq, rfl⟩)
  show Q.map (autOn (tildeOf Z₁ H) W).subtype = ⊥
  rw [hQbot, Subgroup.map_bot]

end Section

end Setup521

end CFSG.Quasithin.H13
