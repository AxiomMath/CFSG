module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.FF81.CentAInvariant
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin CFSG.Open

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

theorem isTwoLocal_centralizer_of_mul_self {s : G} (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    IsTwoLocal (Subgroup.centralizer ({s} : Set G)) := by
  have hpow : s ^ 2 = 1 := by rw [pow_two]; exact hs2
  have hdvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  have hord : orderOf s = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs1
    · exact h
  have hN : Subgroup.normalizer ((Subgroup.zpowers s : Subgroup G) : Set G) =
      Subgroup.centralizer ({s} : Set G) := by
    refine le_antisymm (fun g hg => ?_) ?_
    · have h1 : g * s * g⁻¹ ∈ Subgroup.zpowers s :=
        (Subgroup.mem_normalizer_iff.mp hg s).mp (Subgroup.mem_zpowers s)
      have h1ne : g * s * g⁻¹ ≠ 1 := by
        intro h
        apply hs1
        calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h]
          _ = 1 := by simp
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      have hkne : s ^ k ≠ 1 := by rw [hk]; exact h1ne
      have hz : g * s * g⁻¹ = s := by
        rw [← hk, ← zpow_mod_orderOf s k, hord, Nat.cast_ofNat]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · exfalso
          apply hkne
          rw [← zpow_mod_orderOf s k, hord, Nat.cast_ofNat, h, zpow_zero]
        · rw [h, zpow_one]
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * s = (g * s * g⁻¹) * g := by group
        _ = s * g := by rw [hz]
    · rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
  refine ⟨Subgroup.zpowers s, ?_, ?_, hN.symm⟩
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])

private theorem caO2_t_mul_self (hS : CentASetting m Y L R b t φ) : t * t = 1 := by
  have h1 : (⟨t, hS.t_mem⟩ : ↥Y) * ⟨t, hS.t_mem⟩ = 1 := by
    apply φ.injective
    rw [map_mul, hS.φ_t, jGL_mul_self, map_one]
  simpa using congrArg Subtype.val h1

private theorem caO2_t_ne_one (hS : CentASetting m Y L R b t φ) : t ≠ 1 := by
  intro h
  have h1 : (⟨t, hS.t_mem⟩ : ↥Y) = 1 := Subtype.ext h
  have h2 : jGL 1 m = 1 := by rw [← hS.φ_t, h1, map_one]
  have h3 : uGL (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) 0
      (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) =
      uGL (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) 0
        (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) := by
    simpa [jGL, uGL_zero] using h2
  exact one_ne_zero (uGL_injective h3).2.2

private theorem caO2_liftSub_zSub (hS : CentASetting m Y L R b t φ) :
    liftSub φ (zSub 1 m) = Subgroup.zpowers t := by
  have hsymm : φ.symm.toMonoidHom (jGL 1 m) = (⟨t, hS.t_mem⟩ : ↥Y) := by
    change φ.symm (jGL 1 m) = (⟨t, hS.t_mem⟩ : ↥Y)
    rw [← hS.φ_t, MulEquiv.symm_apply_apply]
  rw [liftSub, zSub_eq_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hsymm]
  rfl

private theorem caO2_commutator_mem_zSub {u v : G}
    (hu : u ∈ liftSub φ (uSub 1 m)) (hv : v ∈ liftSub φ (uSub 1 m)) :
    u * v * u⁻¹ * v⁻¹ ∈ liftSub φ (zSub 1 m) := by
  obtain ⟨huY, hφu⟩ := (mem_liftSub (φ := φ)).mp hu
  obtain ⟨hvY, hφv⟩ := (mem_liftSub (φ := φ)).mp hv
  have hwY : u * v * u⁻¹ * v⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem huY hvY) (Y.inv_mem huY)) (Y.inv_mem hvY)
  rw [mem_liftSub]
  refine ⟨hwY, ?_⟩
  have hsub : (⟨u * v * u⁻¹ * v⁻¹, hwY⟩ : ↥Y) =
      ⟨u, huY⟩ * ⟨v, hvY⟩ * ⟨u, huY⟩⁻¹ * ⟨v, hvY⟩⁻¹ := by
    ext
    rfl
  rw [hsub]
  simpa only [map_mul, map_inv] using commutator_mem_zSub hφu hφv

private def caO2_commutatorSubgroup (H T Z : Subgroup G)
    (hZc : ∀ g ∈ H, ∀ z ∈ Z, g * z = z * g) : Subgroup G where
  carrier := {h | h ∈ H ∧ ∀ x ∈ T, h * x * h⁻¹ * x⁻¹ ∈ Z}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    intro x _
    simp
  mul_mem' := by
    rintro h k ⟨hhH, hh⟩ ⟨hkH, hk⟩
    refine ⟨H.mul_mem hhH hkH, ?_⟩
    intro x hx
    set z : G := k * x * k⁻¹ * x⁻¹ with hzdef
    set w : G := h * x * h⁻¹ * x⁻¹ with hwdef
    have hz : z ∈ Z := hk x hx
    have hw : w ∈ Z := hh x hx
    have hkx : k * x * k⁻¹ = z * x := by rw [hzdef]; group
    have hhz : h * z = z * h := hZc h hhH z hz
    have key : (h * k) * x * (h * k)⁻¹ * x⁻¹ = z * w := by
      calc
        (h * k) * x * (h * k)⁻¹ * x⁻¹ =
            h * (k * x * k⁻¹) * h⁻¹ * x⁻¹ := by group
        _ = h * (z * x) * h⁻¹ * x⁻¹ := by rw [hkx]
        _ = (h * z * h⁻¹) * (h * x * h⁻¹) * x⁻¹ := by group
        _ = z * (h * x * h⁻¹) * x⁻¹ := by rw [hhz]; group
        _ = z * (h * x * h⁻¹ * x⁻¹) := by group
        _ = z * w := by rw [hwdef]
    rw [key]
    exact Z.mul_mem hz hw
  inv_mem' := by
    rintro h ⟨hhH, hh⟩
    refine ⟨H.inv_mem hhH, ?_⟩
    intro x hx
    set z : G := h * x * h⁻¹ * x⁻¹ with hzdef
    have hz : z ∈ Z := hh x hx
    have hzinv : h⁻¹ * z = z * h⁻¹ :=
      (show Commute h z from hZc h hhH z hz).inv_left.eq
    have hxconj : h * x * h⁻¹ = z * x := by rw [hzdef]; group
    have h1 : x = z * (h⁻¹ * x * h) := by
      calc
        x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = h⁻¹ * (z * x) * h := by rw [hxconj]
        _ = (h⁻¹ * z) * (x * h) := by group
        _ = (z * h⁻¹) * (x * h) := by rw [hzinv]
        _ = z * (h⁻¹ * x * h) := by group
    have key : h⁻¹ * x * h = z⁻¹ * x := by
      calc
        h⁻¹ * x * h = z⁻¹ * (z * (h⁻¹ * x * h)) := by group
        _ = z⁻¹ * x := by rw [← h1]
    have hgoal : h⁻¹ * x * (h⁻¹)⁻¹ * x⁻¹ = z⁻¹ := by
      calc
        h⁻¹ * x * (h⁻¹)⁻¹ * x⁻¹ = h⁻¹ * x * h * x⁻¹ := by group
        _ = (z⁻¹ * x) * x⁻¹ := by rw [key]
        _ = z⁻¹ := by group
    rw [hgoal]
    exact Z.inv_mem hz

private theorem caO2_commutatorSubgroup_normal {H T Z : Subgroup G}
    (hTn : ∀ g ∈ H, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hZc : ∀ g ∈ H, ∀ z ∈ Z, g * z = z * g) :
    ∀ g ∈ H, ∀ x ∈ caO2_commutatorSubgroup H T Z hZc,
      g * x * g⁻¹ ∈ caO2_commutatorSubgroup H T Z hZc := by
  intro g hg x hx
  refine ⟨H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg), ?_⟩
  intro y hy
  have hy' : g⁻¹ * y * g ∈ T := by
    simpa using hTn g⁻¹ (H.inv_mem hg) y hy
  have hz : x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹ ∈ Z := hx.2 _ hy'
  have key : (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
      g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
  rw [key]
  have hgz : g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
      x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹ := by
    have hzc := hZc g hg _ hz
    rw [hzc]; group
  rw [hgz]
  exact hz

private theorem caO2_commutatorSubgroup_isPGroup {H T Z : Subgroup G}
    (hcharT : H ⊓ Subgroup.centralizer (T : Set G) ≤ T)
    (hT2 : IsPGroup 2 T)
    (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hZc : ∀ g ∈ H, ∀ z ∈ Z, g * z = z * g) :
    IsPGroup 2 (caO2_commutatorSubgroup H T Z hZc) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro h
  have hhH : (h : G) ∈ H := h.2.1
  have hcond : ∀ x ∈ T, (h : G) * x * (h : G)⁻¹ * x⁻¹ ∈ Z := h.2.2
  have hsqT : (h : G) * (h : G) ∈ T := by
    refine hcharT ⟨H.mul_mem hhH hhH, ?_⟩
    change (h : G) * (h : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    set z : G := (h : G) * x * (h : G)⁻¹ * x⁻¹ with hzdef
    have hz : z ∈ Z := hcond x hx
    have hxconj : (h : G) * x * (h : G)⁻¹ = z * x := by rw [hzdef]; group
    have hsqconj : ((h : G) * (h : G)) * x * ((h : G) * (h : G))⁻¹ = x := by
      calc
        ((h : G) * (h : G)) * x * ((h : G) * (h : G))⁻¹
            = (h : G) * ((h : G) * x * (h : G)⁻¹) * (h : G)⁻¹ := by group
        _ = (h : G) * (z * x) * (h : G)⁻¹ := by rw [hxconj]
        _ = ((h : G) * z * (h : G)⁻¹) * ((h : G) * x * (h : G)⁻¹) := by group
        _ = z * ((h : G) * x * (h : G)⁻¹) := by
              have hzh : (h : G) * z * (h : G)⁻¹ = z := by
                rw [hZc (h : G) hhH z hz]; group
              rw [hzh]
        _ = z * (z * x) := by rw [hxconj]
        _ = x := by rw [← mul_assoc, hZ2 z hz, one_mul]
    have hsqmul : ((h : G) * (h : G)) * x = x * ((h : G) * (h : G)) := by
      calc
        ((h : G) * (h : G)) * x =
            (((h : G) * (h : G)) * x * ((h : G) * (h : G))⁻¹) *
              ((h : G) * (h : G)) := by group
        _ = x * ((h : G) * (h : G)) := by rw [hsqconj]
    exact hsqmul.symm
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hT2)
    (⟨(h : G) * (h : G), hsqT⟩ : ↥T)
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  have hk' : ((h : G) * (h : G)) ^ 2 ^ k = 1 := by
    simpa using congrArg (fun x : ↥T => (x : G)) hk
  calc
    (h : G) ^ 2 ^ (k + 1) = (h : G) ^ (2 * 2 ^ k) := by
      rw [show 2 ^ (k + 1) = 2 * 2 ^ k from pow_succ' 2 k]
    _ = ((h : G) ^ 2) ^ 2 ^ k := by rw [pow_mul]
    _ = ((h : G) * (h : G)) ^ 2 ^ k := by rw [pow_two]
    _ = 1 := hk'

private theorem caO2_le_pCoreOf {H N : Subgroup G} (hNH : N ≤ H)
    (hNn : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hN2 : IsPGroup 2 N) :
    N ≤ pCoreOf 2 H := by
  have hnormal : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hNH).mpr fun n g hn hg => hNn g hg n hn
  have h2 : IsPGroup 2 (N.subgroupOf H) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  intro n hn
  rw [pCoreOf]
  refine Subgroup.mem_map.mpr ⟨⟨n, hNH hn⟩, ?_, rfl⟩
  rw [CFSG.pCore_eq_iSup]
  exact Subgroup.mem_iSup_of_mem (N.subgroupOf H)
    (Subgroup.mem_iSup_of_mem hnormal
      (Subgroup.mem_iSup_of_mem h2 (Subgroup.mem_subgroupOf.mpr hn)))

private theorem caO2_pCoreOf_le (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H := by
  rw [pCoreOf]
  exact Subgroup.map_subtype_le _

private theorem caO2_pCoreOf_isPGroup (p : ℕ) (H : Subgroup G) :
    IsPGroup p (pCoreOf p H) := by
  rw [pCoreOf]
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

private theorem caO2_pCoreOf_normal {p : ℕ} {H : Subgroup G} {g x : G} (hg : g ∈ H)
    (hx : x ∈ pCoreOf p H) : g * x * g⁻¹ ∈ pCoreOf p H := by
  rw [pCoreOf] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem y hy ⟨g, hg⟩, rfl⟩

theorem pCoreOf_centralizer_eq (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ) :
    pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) = liftSub φ (uSub 1 m) := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let U : Subgroup G := liftSub φ (uSub 1 m)
  let T : Subgroup G := pCoreOf 2 H
  let Z : Subgroup G := Subgroup.zpowers t
  have htsq : t * t = 1 := caO2_t_mul_self hS
  have htpow : t ^ 2 = 1 := by rw [pow_two]; exact htsq
  have ht_ne : t ≠ 1 := caO2_t_ne_one hS
  have hH2 : IsTwoLocal H := isTwoLocal_centralizer_of_mul_self ht_ne htsq
  have hT2 : IsPGroup 2 T := caO2_pCoreOf_isPGroup 2 H
  have hTH : T ≤ H := caO2_pCoreOf_le 2 H
  have hTn : ∀ g ∈ H, ∀ x ∈ T, g * x * g⁻¹ ∈ T :=
    fun g hg x hx => caO2_pCoreOf_normal hg hx
  have hZ_eq : liftSub φ (zSub 1 m) = Z := caO2_liftSub_zSub hS
  have hZcomm : ∀ g ∈ H, ∀ z ∈ Z, g * z = z * g := by
    intro g hg z hz
    dsimp [H] at hg
    have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk]
    exact (Commute.zpow_right hgt k).eq
  have hZ2 : ∀ z ∈ Z, z * z = 1 := by
    intro z hz
    have hdvd : orderOf z ∣ 2 :=
      (orderOf_dvd_of_mem_zpowers hz).trans (orderOf_dvd_of_pow_eq_one htpow)
    have h2 : z ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    simpa [pow_two] using h2
  have hUH : U ≤ H := by
    intro u hu
    have huC : u ∈ liftSub φ (Cent 1 m) := liftSub_mono (uSub_le_cent 1 m) hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((mem_liftSub_cent hS).mp huC).2
  have hUZ : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ Z := by
    intro u hu v hv
    rw [← hZ_eq]
    exact caO2_commutator_mem_zSub hu hv
  have hTU : T ≤ U := by
    refine le_liftSub_uSub_of_invariant hS hT2 hTH ?_
    intro y hy x hx
    have hyH : y ∈ H :=
      Subgroup.mem_centralizer_singleton_iff.mpr ((mem_liftSub_cent hS).mp hy).2
    exact hTn y hyH x hx
  have hcharT : H ⊓ Subgroup.centralizer (T : Set G) ≤ T := by
    simpa [T] using hchar H hH2
  let U' : Subgroup G := caO2_commutatorSubgroup H T Z hZcomm
  have hU'normal : ∀ g ∈ H, ∀ x ∈ U', g * x * g⁻¹ ∈ U' :=
    caO2_commutatorSubgroup_normal hTn hZcomm
  have hU'2 : IsPGroup 2 U' :=
    caO2_commutatorSubgroup_isPGroup hcharT hT2 hZ2 hZcomm
  have hU'T : U' ≤ T := by
    have h := caO2_le_pCoreOf (H := H) (N := U') (fun x hx => hx.1) hU'normal hU'2
    simpa [T] using h
  have hUT : U ≤ T := by
    intro u hu
    apply hU'T
    refine ⟨hUH hu, ?_⟩
    intro x hx
    exact hUZ u hu x (hTU hx)
  exact le_antisymm hTU hUT

theorem conj_mem_liftSub_uSub (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ)
    {h u : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G)) (hu : u ∈ liftSub φ (uSub 1 m)) :
    h * u * h⁻¹ ∈ liftSub φ (uSub 1 m) := by
  have hTU : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) = liftSub φ (uSub 1 m) :=
    pCoreOf_centralizer_eq hchar hS
  have huT : u ∈ pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) := by
    rw [hTU]
    exact hu
  have hmem := caO2_pCoreOf_normal hh huT
  rwa [hTU] at hmem

theorem mem_liftSub_uSub_of_commutator (hchar : IsCharTwoType G)
    (hS : CentASetting m Y L R b t φ) {h : G} (hh : h ∈ Subgroup.centralizer ({t} : Set G))
    (hc : ∀ u ∈ liftSub φ (uSub 1 m), h * u * h⁻¹ * u⁻¹ ∈ Subgroup.zpowers t) :
    h ∈ liftSub φ (uSub 1 m) := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let U : Subgroup G := liftSub φ (uSub 1 m)
  let T : Subgroup G := pCoreOf 2 H
  let Z : Subgroup G := Subgroup.zpowers t
  have htsq : t * t = 1 := caO2_t_mul_self hS
  have htpow : t ^ 2 = 1 := by rw [pow_two]; exact htsq
  have ht_ne : t ≠ 1 := caO2_t_ne_one hS
  have hH2 : IsTwoLocal H := isTwoLocal_centralizer_of_mul_self ht_ne htsq
  have hT2 : IsPGroup 2 T := caO2_pCoreOf_isPGroup 2 H
  have hTn : ∀ g ∈ H, ∀ x ∈ T, g * x * g⁻¹ ∈ T :=
    fun g hg x hx => caO2_pCoreOf_normal hg hx
  have hZcomm : ∀ g ∈ H, ∀ z ∈ Z, g * z = z * g := by
    intro g hg z hz
    dsimp [H] at hg
    have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk]
    exact (Commute.zpow_right hgt k).eq
  have hZ2 : ∀ z ∈ Z, z * z = 1 := by
    intro z hz
    have hdvd : orderOf z ∣ 2 :=
      (orderOf_dvd_of_mem_zpowers hz).trans (orderOf_dvd_of_pow_eq_one htpow)
    have h2 : z ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    simpa [pow_two] using h2
  have hcharT : H ⊓ Subgroup.centralizer (T : Set G) ≤ T := by
    simpa [T] using hchar H hH2
  have hTU : T = U := by
    simpa [T, U, H] using pCoreOf_centralizer_eq hchar hS
  let U' : Subgroup G := caO2_commutatorSubgroup H T Z hZcomm
  have hU'T : U' ≤ T := by
    have h := caO2_le_pCoreOf (H := H) (N := U') (fun x hx => hx.1)
      (caO2_commutatorSubgroup_normal hTn hZcomm)
      (caO2_commutatorSubgroup_isPGroup hcharT hT2 hZ2 hZcomm)
    simpa [T] using h
  have hhH : h ∈ H := hh
  have hU' : h ∈ U' := by
    refine ⟨hhH, ?_⟩
    intro x hx
    have hxU : x ∈ U := by
      rw [← hTU]
      exact hx
    exact hc x hxU
  have hmemT : h ∈ T := hU'T hU'
  rwa [hTU] at hmemT

end CFSG.StandardType.FF81.CentA

end
