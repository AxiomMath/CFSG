module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIbGen
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.Quasithin.Recognition.Stroth.Str86U3MCart2
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_bigB_le_normalizer_z1_inf_q2 (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤
      Subgroup.normalizer ((Z1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
  have hP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hP1.trans ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  have hQ : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  exact CFSG.Quasithin.A1a.le_normalizer_inf hZ hQ

theorem str86_caseIIa_notLe_cartan_false
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {N : Subgroup G} (hN : IsElemAbelian 2 N) (hNZ : N ≤ Z1 L1 L2 S)
    (hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (N : Set G))
    (hSC : S ⊓ Subgroup.centralizer (N : Set G) = Q1 L1 L2 S)
    (hnat : @BinaryNaturalSU3 ↥N (commGroupOfElemAbelian hN) (autOn (L1 ⊔ S) N) ⊤ ⊥ k)
    {t : G} (htS : t ∈ S) (htQ1 : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hYX : Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) ≤ Q2 L1 L2 S)
    (hXY : (Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
      (Z1 L1 L2 S ⊓ Q2 L1 L2 S) = 2 ^ k)
    (hZX : (Z1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (Z1 L1 L2 S) = 2 ^ k) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CommGroup ↥N := commGroupOfElemAbelian hN
  set Z : Subgroup G := Z1 L1 L2 S with hZdef
  set X : Subgroup G := Z ⊓ Q2 L1 L2 S with hXdef
  set Y : Subgroup G := Z ⊓ Subgroup.centralizer ({t} : Set G) with hYdef
  set H : Subgroup G := L1 ⊔ S
  set P₁ : Subgroup G := P1 L1 L2 S
  set B : Subgroup G := bigB L1 L2 S
  set Q₁ : Subgroup G := Q1 L1 L2 S
  have hSleB : S ≤ B := le_sup_right
  have hSP1 : S ≤ P₁ := hSleB.trans le_sup_right
  have hHP1 : H ≤ P₁ := sup_le le_sup_left hSP1
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := hSP1.trans hNP1
  have htN : t ∈ Subgroup.normalizer (N : Set G) := hSN htS
  have hBNX : B ≤ Subgroup.normalizer (X : Set G) :=
    str86_bigB_le_normalizer_z1_inf_q2 L1 L2 S
  let T : Subgroup (MulAut ↥N) := autOn S N
  let L : Subgroup (MulAut ↥N) := autOn H N
  let u : MulAut ↥N := conjAct N ⟨t, htN⟩
  have hTL : T ≤ L := AutOn.autOn_mono (le_sup_right : S ≤ H)
  have hT : IsPGroup 2 T := AutOn.isPGroup_autOn hF.1.h1.pgroup
  have huT : u ∈ T := AutOn.conjAct_mem_autOn ⟨t, htN⟩ htS
  have hu2 : u * u = 1 := by
    show conjAct N ⟨t, htN⟩ * conjAct N ⟨t, htN⟩ = 1
    rw [← map_mul]
    have hpair : (⟨t, htN⟩ * ⟨t, htN⟩ : Subgroup.normalizer (N : Set G)) = 1 := by
      ext
      simpa using ht2
    rw [hpair, map_one]
  have hu1 : u ≠ 1 := by
    intro h1
    have hc : t ∈ Subgroup.centralizer (N : Set G) :=
      (AutOn.conjAct_eq_one_iff ⟨t, htN⟩).mp h1
    exact htQ1 (hSC ▸ Subgroup.mem_inf.mpr ⟨htS, hc⟩)
  have hTc : (2 ^ k) ^ 3 ≤ Nat.card T := by
    have hcard : Nat.card T = Q₁.relIndex S := by
      show Nat.card (autOn S N) = Q₁.relIndex S
      rw [card_autOn_eq_relIndex hSN, hSC]
    rw [hcard]
    exact le_of_eq (str86_relIndex_q1_s hF hSB hk hFc hU3).symm
  obtain ⟨hidx, htrans⟩ :=
    binaryNaturalSU3_exists_normalizer_mod_fix hk hnat hTL hT hTc huT hu2 hu1
  have hfix : @fixV ↥N (commGroupOfElemAbelian hN) (Subgroup.zpowers u) =
      (Subgroup.centralizer ({t} : Set G)).subgroupOf N := by
    ext w
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h2 := congrArg (fun z : ↥N => (z : G)) h
      rw [show ((u w : ↥N) : G) = t * (w : G) * t⁻¹ from
        AutOn.coe_conjAct_apply N ⟨t, htN⟩ w] at h2
      calc (w : G) * t = (t * (w : G) * t⁻¹) * t := by rw [h2]
        _ = t * (w : G) := by group
    · intro h
      apply Subtype.ext
      rw [show ((u w : ↥N) : G) = t * (w : G) * t⁻¹ from
        AutOn.coe_conjAct_apply N ⟨t, htN⟩ w]
      calc t * (w : G) * t⁻¹ = ((w : G) * t) * t⁻¹ := by rw [h]
        _ = (w : G) := by group
  have hNY : N ⊓ Subgroup.centralizer ({t} : Set G) = N ⊓ Y := by
    rw [hYdef]
    ext x
    constructor
    · rintro ⟨hxN, hxC⟩
      exact ⟨hxN, hNZ hxN, hxC⟩
    · rintro ⟨hxN, -, hxC⟩
      exact ⟨hxN, hxC⟩
  have hidxN : (2 ^ k) ^ 2 ≤ (N ⊓ Y).relIndex N := by
    rw [← hNY, Subgroup.inf_relIndex_left]
    refine le_trans hidx (le_of_eq ?_)
    rw [hfix, ← Subgroup.relIndex_top_right
        (H := (Subgroup.centralizer ({t} : Set G)).subgroupOf N),
      ← Subgroup.subgroupOf_self N,
      Subgroup.relIndex_subgroupOf (H := Subgroup.centralizer ({t} : Set G))
        (K := N) (L := N) le_rfl]
  have hYX' : Y ≤ X := by
    rw [hYdef, hXdef]
    exact le_inf inf_le_left hYX
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNX : ¬ N ≤ X := by
    intro hNXle
    have h1 : (N ⊓ Y).relIndex N ≤ Y.relIndex X :=
      relIndex_le_of_inf_centralizer_le hNXle inf_le_left hYX' (by rw [inf_comm])
    have hle : (2 ^ k) ^ 2 ≤ 2 ^ k := by
      calc (2 ^ k) ^ 2 ≤ (N ⊓ Y).relIndex N := hidxN
        _ ≤ Y.relIndex X := h1
        _ = 2 ^ k := by simpa [hYdef, hXdef, hZdef] using hXY
    nlinarith
  obtain ⟨w₂, hw₂X⟩ : ∃ w : ↥N, (w : G) ∉ X := by
    by_contra hcon
    push Not at hcon
    exact hNX fun x hx => hcon ⟨x, hx⟩
  obtain ⟨w₁, hw₁X, hw₁C⟩ : ∃ w : ↥N,
      (w : G) ∈ X ∧ (w : G) ∉ Subgroup.centralizer ({t} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : N ⊓ X ≤ Subgroup.centralizer ({t} : Set G) := by
      rintro x ⟨hxN, hxX⟩
      exact hcon ⟨x, hxN⟩ hxX
    have heq : N ⊓ Y = N ⊓ X := by
      refine le_antisymm (inf_le_inf_left N hYX') ?_
      exact le_inf inf_le_left (le_inf ((inf_le_left : N ⊓ X ≤ N).trans hNZ) hle)
    have h1 : (N ⊓ X).relIndex N ≤ X.relIndex Z :=
      relIndex_le_of_inf_centralizer_le hNZ inf_le_left inf_le_left (by rw [inf_comm])
    have hle2 : (2 ^ k) ^ 2 ≤ 2 ^ k := by
      calc (2 ^ k) ^ 2 ≤ (N ⊓ Y).relIndex N := hidxN
        _ = (N ⊓ X).relIndex N := by rw [heq]
        _ ≤ X.relIndex Z := h1
        _ = 2 ^ k := by simpa [hXdef, hZdef] using hZX
    nlinarith
  have hu_ne_w₁ : u w₁ ≠ w₁ := by
    intro h
    apply hw₁C
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := congrArg (fun z : ↥N => (z : G)) h
    rw [show ((u w₁ : ↥N) : G) = t * (w₁ : G) * t⁻¹ from
      AutOn.coe_conjAct_apply N ⟨t, htN⟩ w₁] at h2
    calc (w₁ : G) * t = (t * (w₁ : G) * t⁻¹) * t := by rw [h2]
      _ = t * (w₁ : G) := by group
  have hu_ne_w₂ : u w₂ ≠ w₂ := by
    intro h
    apply hw₂X
    have h2 := congrArg (fun z : ↥N => (z : G)) h
    rw [show ((u w₂ : ↥N) : G) = t * (w₂ : G) * t⁻¹ from
      AutOn.coe_conjAct_apply N ⟨t, htN⟩ w₂] at h2
    have hc : (w₂ : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (w₂ : G) * t = (t * (w₂ : G) * t⁻¹) * t := by rw [h2]
        _ = t * (w₂ : G) := by group
    have hmem : (w₂ : G) ∈ N ⊓ Y :=
      Subgroup.mem_inf.mpr ⟨w₂.2, ⟨hNZ w₂.2, hc⟩⟩
    exact hYX' (Subgroup.mem_inf.mp hmem).2
  have htrans' := htrans w₁ w₂ hu_ne_w₁ hu_ne_w₂
  obtain ⟨n, hn⟩ := htrans'
  have hnL : n ∈ L := (Subgroup.mem_inf.mp hn.1).1
  have hnT : n ∈ Subgroup.normalizer (T : Set (MulAut ↥N)) := (Subgroup.mem_inf.mp hn.1).2
  have hfixn : u (n w₁ * w₂⁻¹) = n w₁ * w₂⁻¹ := hn.2
  let NG : Subgroup G := Subgroup.normalizer (N : Set G)
  let ψ : ↥NG →* MulAut ↥N := conjAct N
  obtain ⟨x, hxH, hxψ⟩ : ∃ x : ↥NG, (x : G) ∈ H ∧ ψ x = n := by
    have hnL' : n ∈ autOn H N := hnL
    obtain ⟨x, hx, hxe⟩ := AutOn.mem_autOn_iff.mp hnL'
    exact ⟨x, hx, hxe⟩
  let Tp : Subgroup G := (T.comap ψ).map NG.subtype
  let NTp : Subgroup G :=
    ((Subgroup.normalizer (T : Set (MulAut ↥N))).comap ψ).map NG.subtype
  let O : Subgroup G := P₁ ⊓ Tp
  let H' : Subgroup G := P₁ ⊓ NTp
  have hSO : S ≤ O := by
    intro s hs
    refine Subgroup.mem_inf.mpr ⟨hSP1 hs, ?_⟩
    exact Subgroup.mem_map.mpr ⟨⟨s, hSN hs⟩, AutOn.conjAct_mem_autOn ⟨s, hSN hs⟩ hs, rfl⟩
  have hOP1 : O ≤ P₁ := inf_le_left
  have hOH' : O ≤ H' := by
    refine inf_le_inf_left P₁ ?_
    exact Subgroup.map_mono (f := NG.subtype) (fun y hy => Subgroup.le_normalizer hy)
  have hNT : NTp ≤ Subgroup.normalizer (Tp : Set G) := by
    have key : ∀ (y : ↥NG), ψ y ∈ Subgroup.normalizer (T : Set (MulAut ↥N)) →
        ∀ z : G, z ∈ Tp → (y : G) * z * (y : G)⁻¹ ∈ Tp := by
      intro y hy z hz
      obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨y * z₀ * y⁻¹, ?_, rfl⟩
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy (ψ z₀)).mp hz₀
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨key y₀ hy₀ z, fun hz => ?_⟩
    have hy₀' : ψ y₀⁻¹ ∈ Subgroup.normalizer (T : Set (MulAut ↥N)) := by
      rw [map_inv]
      exact (Subgroup.normalizer (T : Set (MulAut ↥N))).inv_mem (Subgroup.mem_comap.mp hy₀)
    have h := key y₀⁻¹ hy₀' ((y₀ : G) * z * (y₀ : G)⁻¹) hz
    rwa [show ((y₀⁻¹ : ↥NG) : G) * ((y₀ : G) * z * (y₀ : G)⁻¹) *
        (((y₀⁻¹ : ↥NG) : G))⁻¹ = z by simp only [Subgroup.coe_inv]; group] at h
  have hH'O : H' ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.Quasithin.A1a.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans hNT)
  have hOnorm : (O.subgroupOf H').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH').mpr hH'O
  have hSylP1 : CFSG.Quasithin.IsSylowIn 2 S P₁ := by
    refine ⟨hSP1, hF.1.h1.pgroup, ?_⟩
    have h := (f112_isSylowTwoOf_P1 hF.toW).2.2
    rwa [← Subgroup.relIndex_top_right (H := S.subgroupOf P₁), ← Subgroup.subgroupOf_self P₁,
      Subgroup.relIndex_subgroupOf (H := S) (K := P₁) (L := P₁) le_rfl] at h
  have hSylO : CFSG.Quasithin.IsSylowIn 2 S O :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_of_le_of_le hSylP1 hSO hOP1
  have hxH' : (x : G) ∈ H' := by
    refine Subgroup.mem_inf.mpr ⟨hHP1 hxH, ?_⟩
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_comap, hxψ]
    exact hnT
  obtain ⟨y, hyO, d, hd, hxd⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.frattini_argument hOH' hOnorm hSylO hxH'
  have hyP1 : y ∈ P₁ := hOP1 hyO
  have hyNG : y ∈ NG := hNP1 hyP1
  have hdP1 : d ∈ P₁ := by
    have hde : d = y⁻¹ * (x : G) := by rw [hxd]; group
    rw [hde]
    exact P₁.mul_mem (P₁.inv_mem hyP1) (hHP1 hxH)
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.mp hd).2
  have hdB : d ∈ B :=
    str86_p1_inf_normalizer_le_bigB hF.toW hSB (Subgroup.mem_inf.mpr ⟨hdP1, hdS⟩)
  have hdNG : d ∈ NG := hNP1 hdP1
  have hdNX : d ∈ Subgroup.normalizer (X : Set G) := hBNX hdB
  have hyT : ψ ⟨y, hyNG⟩ ∈ T := by
    obtain ⟨y₀, hy₀, hyeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hyO).2
    have hye : y₀ = ⟨y, hyNG⟩ := Subtype.ext hyeq
    rwa [hye] at hy₀
  obtain ⟨s, hsS, hψs⟩ : ∃ s : ↥NG, (s : G) ∈ S ∧ ψ s = ψ ⟨y, hyNG⟩ := by
    obtain ⟨s, hs, hse⟩ :=
      Subgroup.mem_map.mp (show ψ ⟨y, hyNG⟩ ∈ (S.subgroupOf NG).map ψ from hyT)
    exact ⟨s, hs, hse⟩
  have hsNX : (s : G) ∈ Subgroup.normalizer (X : Set G) := hBNX (hSleB hsS)
  have hkey : ∀ w : ↥N,
      ((conjAct N ⟨d, hdNG⟩) w : G) = (s : G)⁻¹ * ((n w : ↥N) : G) * (s : G) := by
    intro w
    have hd_eq : d = y⁻¹ * (x : G) := by rw [hxd]; group
    have e1 : (⟨d, hdNG⟩ : ↥NG) = ⟨y, hyNG⟩⁻¹ * x := by
      ext
      simpa using hd_eq
    have h2 : ψ ⟨d, hdNG⟩ = (ψ ⟨y, hyNG⟩)⁻¹ * n := by
      rw [e1, map_mul, map_inv, hxψ]
    have h3 : conjAct N ⟨d, hdNG⟩ = (conjAct N s)⁻¹ * n := by
      rw [show conjAct N ⟨d, hdNG⟩ = ψ ⟨d, hdNG⟩ from rfl, h2, ← hψs]
    have h4 : (conjAct N s)⁻¹ = conjAct N s⁻¹ := by rw [← map_inv]
    rw [h3, h4, MulAut.mul_apply, AutOn.coe_conjAct_apply]
    simp only [Subgroup.coe_inv, inv_inv]
  have hnw₁X : ((n w₁ : ↥N) : G) ∈ X := by
    have hdX : d * (w₁ : G) * d⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hdNX (w₁ : G)).mp hw₁X
    have hdX' : ((conjAct N ⟨d, hdNG⟩) w₁ : G) ∈ X := by
      rw [AutOn.coe_conjAct_apply]
      exact hdX
    have h1 : (s : G)⁻¹ * ((n w₁ : ↥N) : G) * (s : G) ∈ X := by
      rw [← hkey w₁]
      exact hdX'
    refine (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (X : Set G)).inv_mem hsNX) ((n w₁ : ↥N) : G)).mpr ?_
    simpa using h1
  have hmemC : ((n w₁ * w₂⁻¹ : ↥N) : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    have hv := congrArg (fun z : ↥N => (z : G)) hfixn
    have h' : t * ((n w₁ * w₂⁻¹ : ↥N) : G) * t⁻¹ = ((n w₁ * w₂⁻¹ : ↥N) : G) := by
      have h1 : ((u (n w₁ * w₂⁻¹) : ↥N) : G) =
          t * ((n w₁ * w₂⁻¹ : ↥N) : G) * t⁻¹ :=
        AutOn.coe_conjAct_apply N ⟨t, htN⟩ (n w₁ * w₂⁻¹)
      rw [hv] at h1
      exact h1.symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((n w₁ * w₂⁻¹ : ↥N) : G) * t
        = (t * ((n w₁ * w₂⁻¹ : ↥N) : G) * t⁻¹) * t := by rw [h']
      _ = t * ((n w₁ * w₂⁻¹ : ↥N) : G) := by group
  have hNmem : ((n w₁ * w₂⁻¹ : ↥N) : G) ∈ N := (n w₁ * w₂⁻¹).2
  have hmemY : ((n w₁ * w₂⁻¹ : ↥N) : G) ∈ N ⊓ Y :=
    Subgroup.mem_inf.mpr ⟨hNmem, Subgroup.mem_inf.mpr ⟨hNZ hNmem, hmemC⟩⟩
  have hmemX : ((n w₁ * w₂⁻¹ : ↥N) : G) ∈ X :=
    hYX' (Subgroup.mem_inf.mp hmemY).2
  have hw₂mem : (w₂ : G) ∈ X := by
    have hv : (w₂ : G) =
        (((n w₁ : ↥N) : G)⁻¹ * ((n w₁ * w₂⁻¹ : ↥N) : G))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hv]
    exact X.inv_mem (X.mul_mem (X.inv_mem hnw₁X) hmemX)
  exact hw₂X hw₂mem

end CFSG.Quasithin.Stroth

end
