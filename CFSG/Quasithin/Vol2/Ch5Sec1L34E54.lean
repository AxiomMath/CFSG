module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34E54NoFF
public import CFSG.Quasithin.Vol2.KGFactL34Aut
public import CFSG.Quasithin.Background.VolIE54
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsVolI

public section

namespace CFSG.Quasithin.H13.E54

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Core

variable {H : Type} [Group H]

theorem pCore_subgroupOf_le_pCore (N : Subgroup H) [N.Normal] :
    (CFSG.pCore 2 H).subgroupOf N ≤ CFSG.pCore 2 ↥N :=
  le_sSup ⟨inferInstance, (CFSG.pCore_isPGroup (p := 2) (G := H)).comap_subtype⟩

theorem pCore_quotient_pCore_eq_bot : CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set Q := CFSG.pCore 2 H with hQ
  set O := CFSG.pCore 2 (H ⧸ Q) with hO
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hK : IsPGroup 2 ↥(O.comap π) := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := H ⧸ Q)).comap_of_ker_isPGroup π ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := H)
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKQ : O.comap π ≤ Q := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ Q.map π := Subgroup.map_mono hKQ
    _ = ⊥ := QuotientGroup.map_mk'_self Q

theorem pCoreOf_top : pCoreOf 2 (⊤ : Subgroup H) = CFSG.pCore 2 H := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := H)).symm,
    Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := H)).symm.toMonoidHom =
      MonoidHom.id H := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

end Core

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {X K P : Subgroup Γ}

omit [Finite Γ] in
theorem mem_pCore_iff (x : ↥X) : x ∈ CFSG.pCore 2 ↥X ↔ (x : Γ) ∈ pCoreOf 2 X :=
  (CFSG.mem_openPCoreOf_iff x).symm

omit [Finite Γ] in
theorem lieModel_subgroupOf (hKX : K ≤ X) (hK : LieModel (O2Q K) .PSL 3 2 2) :
    LieModel (↥(K.subgroupOf X) ⧸ CFSG.pCore 2 ↥(K.subgroupOf X)) .PSL 3 2 2 := by
  set e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have hmap : (CFSG.pCore 2 ↥(K.subgroupOf X)).map e.toMonoidHom = CFSG.pCore 2 ↥K := by
    exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ e hmap).symm hK

omit [Finite Γ] in
theorem exists_two_pow_mem (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hP : IsPGroup 2 P) (hX : X = K ⊔ P) (y : ↥X) : ∃ e : ℕ, y ^ 2 ^ e ∈ K.subgroupOf X := by
  have hPX : P ≤ X := hX ▸ le_sup_right
  have hset : ((K ⊔ P : Subgroup Γ) : Set Γ) = (K : Set Γ) * (P : Set Γ) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hPX.trans hXK)
  have hy : (y : Γ) ∈ (K : Set Γ) * (P : Set Γ) := by
    rw [← hset, ← hX]
    exact y.2
  obtain ⟨k, hk, p, hp, hkp⟩ := Set.mem_mul.mp hy
  obtain ⟨e, he⟩ := hP ⟨p, hp⟩
  refine ⟨e, ?_⟩
  have : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  have h1 : (QuotientGroup.mk y : ↥X ⧸ K.subgroupOf X) =
      QuotientGroup.mk (⟨p, hPX hp⟩ : ↥X) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hpN : p⁻¹ ∈ Subgroup.normalizer (K : Set Γ) := hXK (X.inv_mem (hPX hp))
    have h2 := (Subgroup.mem_normalizer_iff.mp hpN k⁻¹).mp (K.inv_mem hk)
    have e2 : ((y⁻¹ * ⟨p, hPX hp⟩ : ↥X) : Γ) = p⁻¹ * k⁻¹ * p⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hkp]
      group
    rw [e2]
    exact h2
  rw [h1, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have h3 : (⟨p, hPX hp⟩ : ↥X) ^ 2 ^ e = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val he)
  rw [h3]
  exact Subgroup.one_mem _

theorem inf_pCoreOf_le (hKX : K ≤ X) : K ⊓ pCoreOf 2 X ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hKX hj)⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right)

theorem solvRad_inf_le (hKX : K ≤ X) (hK : LieModel (O2Q K) .PSL 3 2 2) :
    solvRad X ⊓ K ≤ pCoreOf 2 K := by
  set M : Subgroup ↥K := (solvRad X ⊓ K).subgroupOf K with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm k => ?_⟩
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    refine ⟨?_, K.mul_mem (K.mul_mem k.2 hm.2) (K.inv_mem k.2)⟩
    have h1 := (solvRad_normal X).conj_mem ⟨m, solvRad_le X hm.1⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hm.1) ⟨k, hKX k.2⟩
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hMs : Group.IsSolvable ↥M := by
    have := solvRad_isSolvable X
    let f : ↥M →* ↥(solvRad X) :=
      { toFun := fun m => ⟨((m : ↥K) : Γ), (Subgroup.mem_subgroupOf.mp m.2).1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hs : IsSimpleGroup (O2Q K) := isSimpleGroup_of_lieModel hK
  have hMb : (M.map π).Normal := Subgroup.Normal.map hMn π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map π) with hbot | htop
  · intro c hc
    have hcM : (⟨c, hc.2⟩ : ↥K) ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf]
      exact hc
    have h1 : π ⟨c, hc.2⟩ = 1 := by
      have := Subgroup.mem_map_of_mem π hcM
      rw [hbot] at this
      exact this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff] at h1
    exact h1
  · exfalso
    let g : ↥M →* O2Q K := π.comp M.subtype
    have hg : Function.Surjective g := by
      intro q
      have hq : q ∈ M.map π := by
        rw [htop]
        trivial
      obtain ⟨m, hm, rfl⟩ := hq
      exact ⟨⟨m, hm⟩, rfl⟩
    have hsol : Group.IsSolvable (O2Q K) := Group.isSolvable_of_surjective hg
    have hc := IsSimpleGroup.comm_iff_isSolvable.mpr hsol
    let _ : CommGroup (O2Q K) := { (inferInstance : Group (O2Q K)) with mul_comm := hc }
    have hp : (Nat.card (O2Q K)).Prime := IsSimpleGroup.prime_card
    rw [card_of_lieModel hK] at hp
    norm_num at hp

theorem solvRad_le_pCoreOf (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hK : LieModel (O2Q K) .PSL 3 2 2) (hXC : X ⊓ centralizerModO2 K ≤ pCoreOf 2 X) :
    solvRad X ≤ pCoreOf 2 X := by
  intro r hr
  have hrX : r ∈ X := solvRad_le X hr
  refine hXC ⟨hrX, hXK hrX,
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hXK hrX), fun u hu => ?_⟩
  refine solvRad_inf_le hKX hK ⟨?_, ?_⟩
  ·
    have h1 := (solvRad_normal X).conj_mem ⟨r⁻¹, X.inv_mem hrX⟩
      (by rw [Subgroup.mem_subgroupOf]; exact (solvRad X).inv_mem hr) ⟨u, hKX hu⟩
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : u * r⁻¹ * u⁻¹ ∈ solvRad X := by simpa using h1
    have h3 := (solvRad X).mul_mem hr h2
    have e : r * (u * r⁻¹ * u⁻¹) = r * u * r⁻¹ * u⁻¹ := by group
    rwa [e] at h3
  · exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXK hrX) u).mp hu) (K.inv_mem hu)

end Main

section Bar

variable {Γ : Type} [Group Γ] [Finite Γ] {X K P : Subgroup Γ}

theorem isQuasisimple_of_lieModel {L : Type} [Group L] (h : LieModel L .PSL 3 2 2) :
    CFSG.IsQuasisimple L := by
  have hs : IsSimpleGroup L := isSimpleGroup_of_lieModel h
  have hnc : ∃ a b : L, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup L := { (inferInstance : Group L) with mul_comm := hc }
    have hp : (Nat.card L).Prime := IsSimpleGroup.prime_card
    rw [card_of_lieModel h] at hp
    norm_num at hp
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

@[expose] noncomputable def kBar (X K : Subgroup Γ) : Subgroup (O2Q X) :=
  (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))

omit [Finite Γ] in
theorem kBar_normal (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) :
    (kBar X K).Normal := by
  have : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem lieModel_kBar (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hK : LieModel (O2Q K) .PSL 3 2 2) : LieModel ↥(kBar X K) .PSL 3 2 2 := by
  set Kx : Subgroup ↥X := K.subgroupOf X with hKx
  have : Kx.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  let f : ↥Kx →* ↥(kBar X K) := (π.comp Kx.subtype).codRestrict (kBar X K) fun k => ⟨k, k.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfk : ∀ k : ↥Kx, f k = 1 ↔ (k : ↥X) ∈ CFSG.pCore 2 ↥X := by
    intro k
    constructor
    · intro h
      have h1 : π (k : ↥X) = 1 := congrArg Subtype.val h
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    · intro h
      apply Subtype.ext
      show π (k : ↥X) = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h
  have hle : CFSG.pCore 2 ↥Kx ≤ f.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hfk]
    exact map_pCore_le_pCore Kx ⟨k, hk, rfl⟩
  let θ : (↥Kx ⧸ CFSG.pCore 2 ↥Kx) →* ↥(kBar X K) := QuotientGroup.lift _ f hle
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨k, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hθi : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H k =>
      have h1 : f k = 1 := hq
      rw [QuotientGroup.eq_one_iff]
      exact pCore_subgroupOf_le_pCore Kx ((hfk k).mp h1)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (MulEquiv.ofBijective θ ⟨hθi, hθs⟩)
    (lieModel_subgroupOf hKX hK)

omit [Finite Γ] in
theorem exists_two_pow_mem_kBar (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hP : IsPGroup 2 P) (hX : X = K ⊔ P) (q : O2Q X) : ∃ e : ℕ, q ^ 2 ^ e ∈ kBar X K := by
  induction q using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨e, he⟩ := exists_two_pow_mem hKX hXK hP hX y
    exact ⟨e, ⟨_, he, by rw [QuotientGroup.mk'_apply, QuotientGroup.mk_pow]⟩⟩

theorem centralizer_kBar_eq_bot (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hXC : X ⊓ centralizerModO2 K ≤ pCoreOf 2 X) :
    Subgroup.centralizer (kBar X K : Set (O2Q X)) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff]
    refine hXC ⟨x.2, hXK x.2,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hXK x.2), fun u hu => ?_⟩
    have huK : (⟨u, hKX hu⟩ : ↥X) ∈ K.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      exact hu
    have h1 := Subgroup.mem_centralizer_iff.mp hq _ ⟨_, huK, rfl⟩
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, mem_pCore_iff] at h1
    have h2 : (x : Γ) * u * (x : Γ)⁻¹ * u⁻¹ ∈ pCoreOf 2 X := by
      have h3 := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.mul_mem x.2 (hKX hu))
      have h4 := (Subgroup.mem_normalizer_iff.mp h3 _).mp h1
      have e : (x : Γ) * u * ((((⟨u, hKX hu⟩ : ↥X) * x)⁻¹ * (x * ⟨u, hKX hu⟩) : ↥X) : Γ) *
          ((x : Γ) * u)⁻¹ = (x : Γ) * u * (x : Γ)⁻¹ * u⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [e] at h4
    have h5 : (x : Γ) * u * (x : Γ)⁻¹ * u⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXK x.2) u).mp hu) (K.inv_mem hu)
    exact inf_pCoreOf_le hKX ⟨h5, h2⟩

theorem genFitting_eq_kBar (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hK : LieModel (O2Q K) .PSL 3 2 2) (hP : IsPGroup 2 P) (hX : X = K ⊔ P) :
    CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X)) = kBar X K := by
  have hn := kBar_normal hKX hXK
  have hq := isQuasisimple_of_lieModel (lieModel_kBar hKX hXK hK)
  have hO2 : pCoreOf 2 (⊤ : Subgroup (O2Q X)) = ⊥ := by
    rw [pCoreOf_top]
    exact pCore_quotient_pCore_eq_bot
  exact InternalSec.quasithinGenFitting_eq_of_two_pow (Y := (⊤ : Subgroup (O2Q X)))
    (L := kBar X K) le_top (fun y _ l hl => hn.conj_mem l hl y)
    (CFSG.Quasithin.B1Red.isQuasisimple_to_open hq)
    (fun y _ => exists_two_pow_mem_kBar hKX hXK hP hX y) hO2

theorem isQuasisimple_genFitting (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hK : LieModel (O2Q K) .PSL 3 2 2) (hP : IsPGroup 2 P) (hX : X = K ⊔ P) :
    CFSG.IsQuasisimple ↥(CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X))) := by
  rw [genFitting_eq_kBar hKX hXK hK hP hX]
  exact isQuasisimple_of_lieModel (lieModel_kBar hKX hXK hK)

theorem exists_two_pow_mem_genFitting (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hK : LieModel (O2Q K) .PSL 3 2 2) (hP : IsPGroup 2 P) (hX : X = K ⊔ P) (q : O2Q X) :
    ∃ e : ℕ, q ^ 2 ^ e ∈ CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X)) := by
  rw [genFitting_eq_kBar hKX hXK hK hP hX]
  exact exists_two_pow_mem_kBar hKX hXK hP hX q

theorem pRank_two_le_four (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hK : LieModel (O2Q K) .PSL 3 2 2) (hXC : X ⊓ centralizerModO2 K ≤ pCoreOf 2 X) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (O2Q X)) ≤ 4 := by
  have : (kBar X K).Normal := kBar_normal hKX hXK
  have hC := centralizer_kBar_eq_bot hKX hXK hXC
  let c : O2Q X →* MulAut ↥(kBar X K) := MulAut.conjNormal
  have hc : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hmem : q ∈ Subgroup.centralizer (kBar X K : Set (O2Q X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg (fun φ : MulAut ↥(kBar X K) => ((φ ⟨l, hl⟩ : ↥(kBar X K)) : O2Q X)) hq
      simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc l * q = (q * l * q⁻¹) * q := by rw [h1]
        _ = q * l := by group
    rw [hC] at hmem
    exact hmem
  refine CFSG.SectionRank.pRank_le (G := O2Q X) (p := 2) (H := ⊤) (by norm_num)
    fun E _ hE => ?_
  have h1 := l34AutTwoRankFact_holds ↥(kBar X K) (lieModel_kBar hKX hXK hK) (E.map c)
    (CFSG.SectionRank.isElemAbelian_map hE c)
  rwa [Subgroup.card_map_of_injective hc] at h1

theorem hasNoFaithfulFFModulesMod_pCoreOf (h51 : AsB51) (hS : SQTKGroup ↥X) (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hK : LieModel (O2Q K) .PSL 3 2 2)
    (hP : IsPGroup 2 P) (hX : X = K ⊔ P) : HasNoFaithfulFFModulesMod X (pCoreOf 2 X) := by
  intro W _ _ hW ρ hρ
  have : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hker : ρ.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, hρ, mem_pCore_iff]
  have hKl := lieModel_subgroupOf hKX hK
  have hnt : ¬ K.subgroupOf X ≤ ρ.ker := by
    rw [hker]
    intro hle
    have h2 : IsPGroup 2 ↥(K.subgroupOf X) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).to_le hle
    have htop : CFSG.pCore 2 ↥(K.subgroupOf X) = ⊤ := by
      refine top_le_iff.mp (le_sSup ⟨inferInstance, ?_⟩)
      exact h2.of_equiv (Subgroup.topEquiv (G := ↥(K.subgroupOf X))).symm
    have hsub : Subsingleton (↥(K.subgroupOf X) ⧸ CFSG.pCore 2 ↥(K.subgroupOf X)) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [QuotientGroup.eq, htop]
          trivial
    have hc := card_of_lieModel hKl
    rw [Nat.card_of_subsingleton (1 : ↥(K.subgroupOf X) ⧸ CFSG.pCore 2 ↥(K.subgroupOf X))] at hc
    omega
  exact not_isFFModule h51 hS (K.subgroupOf X) hKl (exists_two_pow_mem hKX hXK hP hX) hW ρ hker
    hnt

end Bar

section NoFF

variable {Γ : Type} [Group Γ] [Finite Γ] {X K P : Subgroup Γ}

theorem hasNoFaithfulFFModulesMod_of_le_solvRad (h51 : AsB51) (hS : SQTKGroup ↥X) (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hK : LieModel (O2Q K) .PSL 3 2 2)
    (hP : IsPGroup 2 P) (hX : X = K ⊔ P) (hC : X ⊓ centralizerModO2 K ≤ pCoreOf 2 X)
    (Y : Subgroup Γ) (_ : (Y.subgroupOf X).Normal) (hY1 : pCoreOf 2 X ≤ Y) (hY2 : Y ≤ solvRad X) :
    HasNoFaithfulFFModulesMod X Y := by
  have hY : Y = pCoreOf 2 X := le_antisymm (hY2.trans (solvRad_le_pCoreOf hKX hXK hK hC)) hY1
  rw [hY]
  exact hasNoFaithfulFFModulesMod_pCoreOf h51 hS hKX hXK hK hP hX

end NoFF

theorem e54L34FactSQTK_of_b51 (h51 : AsB51) : E54L34FactSQTK := by
  intro G _ _ X K P hS hc hP hKX hXK hK hX hC
  rcases VolI.AS_I_E_5_4'_holds G X P 4 (by norm_num) hP hc
      (isQuasisimple_genFitting hKX hXK hK hP.2.1 hX)
      (exists_two_pow_mem_genFitting hKX hXK hK hP.2.1 hX) (pRank_two_le_four hKX hXK hK hC)
      (hasNoFaithfulFFModulesMod_of_le_solvRad h51 hS hKX hXK hK hP.2.1 hX hC) with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

end CFSG.Quasithin.H13.E54
