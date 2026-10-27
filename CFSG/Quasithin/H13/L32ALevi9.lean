module

public import CFSG.Quasithin.H13.L32ALevi8
public import CFSG.Quasithin.H13.L32ACSk9
public import CFSG.Quasithin.H13.L32AM51d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Equiv Equiv.Perm
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem Levi.exists_mul_of_mem_sup {L N : Subgroup G} (hN : N ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ L ⊔ N) : ∃ ℓ ∈ L, ∃ n ∈ N, x = ℓ * n := by
  let S : Subgroup G :=
    { carrier := {y | ∃ ℓ ∈ L, ∃ n ∈ N, y = ℓ * n}
      one_mem' := ⟨1, L.one_mem, 1, N.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨ℓ₁, hℓ₁, n₁, hn₁, rfl⟩ ⟨ℓ₂, hℓ₂, n₂, hn₂, rfl⟩
        have hc : n₁ * ℓ₂ * n₁⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hN hn₁) ℓ₂).1 hℓ₂
        exact ⟨ℓ₁ * (n₁ * ℓ₂ * n₁⁻¹), L.mul_mem hℓ₁ hc, n₁ * n₂, N.mul_mem hn₁ hn₂, by group⟩
      inv_mem' := by
        rintro _ ⟨ℓ, hℓ, n, hn, rfl⟩
        have hc : n⁻¹ * ℓ⁻¹ * n⁻¹⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.1 (hN (N.inv_mem hn)) ℓ⁻¹).1 (L.inv_mem hℓ)
        exact ⟨n⁻¹ * ℓ⁻¹ * n⁻¹⁻¹, hc, n⁻¹, N.inv_mem hn, by group⟩ }
  have hLS : L ≤ S := fun ℓ hℓ => ⟨ℓ, hℓ, 1, N.one_mem, (mul_one ℓ).symm⟩
  have hNS : N ≤ S := fun n hn => ⟨1, L.one_mem, n, hn, (one_mul n).symm⟩
  exact sup_le hLS hNS hx

variable [Finite G] {T L V H : Subgroup G}

namespace Levi

theorem fix_of_same {u w p : Lin.SLn 4} {e : Bool} (h1 : w⁻¹ * p ∈ unitriangular 4 (ZMod 2))
    (h2 : p⁻¹ * mact u e p ∈ unitriangular 4 (ZMod 2)) :
    w⁻¹ * mact u e w ∈ unitriangular 4 (ZMod 2) := by
  have h3 : gamE e (p⁻¹ * w) ∈ unitriangular 4 (ZMod 2) := by
    have h4 : p⁻¹ * w ∈ unitriangular 4 (ZMod 2) := by
      have := inv_mem h1
      rwa [_root_.mul_inv_rev, inv_inv] at this
    cases e
    · exact h4
    · exact BinaryParabolic.graphFun_mem_unitriangular h4
  have e1 : w⁻¹ * mact u e w = (w⁻¹ * p) * (p⁻¹ * mact u e p) * gamE e (p⁻¹ * w) := by
    rw [mact_eq, mact_eq, gamE_mul, gamE_inv]
    group
  rw [e1]
  exact mul_mem (mul_mem h1 h2) h3

omit [Finite G] in
theorem autOf_inv (v : Lin.SLn 4) : (autOf v false)⁻¹ = autOf v⁻¹ false := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, autOf_mul]
  simp only [show gamE false v = v from rfl, inv_mul_cancel, Bool.xor_self]
  exact autOf_one

namespace HSide

variable {K V₁ : Subgroup G} {πK : ↥K →* Lin.SLn 4} {a c x : G}
  (C : HSide T L V H K V₁ πK a c x) [IsMulCommutative ↥(conjClosure V H)]
include C

omit [Finite G] [IsMulCommutative ↥(conjClosure V H)] in
theorem R1_of_core {b : G} (hbT : b ∈ T) {u : Lin.SLn 4} {e : Bool}
    (hb : C.β ⟨b, C.hTH hbT⟩ = autOf u e) (hcore : ∀ y ∈ l1 T L V, y⁻¹ * b * y ∈ T) : R1 u e := by
  have key : ∀ y (hy : y ∈ l1 T L V), (πK ⟨y, C.hl1K hy⟩)⁻¹ * mact u e (πK ⟨y, C.hl1K hy⟩) ∈
      unitriangular 4 (ZMod 2) := by
    intro y hy
    obtain ⟨u', hu', e', he'⟩ := C.β_T (hcore y hy)
    have e1 : (⟨y⁻¹ * b * y, C.hTH (hcore y hy)⟩ : ↥H) =
        (⟨y, C.hKH (C.hl1K hy)⟩ : ↥H)⁻¹ * ⟨b, C.hTH hbT⟩ * ⟨y, C.hKH (C.hl1K hy)⟩ := rfl
    rw [e1, map_mul, map_mul, map_inv, C.β_K (C.hl1K hy), hb, autOf_inv, autOf_mul, autOf_mul]
      at he'
    simp only [show ∀ w : Lin.SLn 4, gamE false w = w from fun _ => rfl, Bool.false_xor,
      Bool.xor_false] at he'
    have := (autOf_inj he').1
    rw [mact_eq, ← mul_assoc, this]
    exact hu'
  have hx2 : x * x ∈ l1 T L V := (l1 T L V).mul_mem C.hx C.hx
  have k1 := key x C.hx
  have k2 := key (x * x) hx2
  have e2 : (⟨x * x, C.hl1K hx2⟩ : ↥K) = ⟨x, C.hl1K C.hx⟩ ^ 2 := Subtype.ext (pow_two x).symm
  rw [e2, map_pow] at k2
  rcases C.lam_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fix_of_same h1 k1, fix_of_same h2 k2⟩
  · exact ⟨fix_of_same h2 k2, fix_of_same h1 k1⟩

omit [Finite G] in
theorem f_cl (b : ↥H) (u : ↥(conjClosure V H)) :
    C.model.f b (cl u) = cl (V₁ := V₁) ⟨(b : G) * u * (b : G)⁻¹ * (u : G)⁻¹,
      (conjClosure V H).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure V H b.2) u).mp u.2) ((conjClosure V H).inv_mem u.2)⟩ := by
  rw [Model.f, model_ρ, ρ_cl, cl, cl, cl, ← map_inv, ← map_mul]
  rfl

theorem false_of_offender (hM : C.model.Hyp) {B : Subgroup G}
    (hBR : B ≤ pCoreOf 2 (l1 T L V ⊔ T)) (hBH : B ≤ H) (hBab : IsElemAbelian 2 B)
    (hBO : ¬ B ≤ pCoreOf 2 H)
    (hBq : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ conjClosure V H,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ V₁)
    (hBidx : (centralizerMod V₁ (conjClosure V H) B).relIndex (conjClosure V H) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2)
    (hRT : pCoreOf 2 (l1 T L V ⊔ T) ≤ T) : False := by
  have hRn : l1 T L V ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hcore : ∀ b ∈ B, ∀ y ∈ l1 T L V, y⁻¹ * b * y ∈ T := by
    intro b hb y hy
    apply hRT
    have := (Subgroup.mem_normalizer_iff.mp (hRn (Subgroup.mem_sup_left (inv_mem hy))) b).mp
      (hBR hb)
    simpa using this
  have hBab' := hBab.1
  refine Model.no_offender hM (B := B.subgroupOf H) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    apply Subtype.ext
    have := hBab.2 b (Subgroup.mem_subgroupOf.mp hb)
    rw [pow_two] at this
    exact this
  · intro b hb b' hb'
    exact Subtype.ext (setLike_mul_comm (Subgroup.mem_subgroupOf.mp hb)
      (Subgroup.mem_subgroupOf.mp hb'))
  · intro b hb b' hb' q
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q
    change C.model.ρ b' (C.model.f b (cl u)) = C.model.f b (cl u)
    rw [C.f_cl, model_ρ, ρ_cl, cl_eq_iff]
    exact hBq b (Subgroup.mem_subgroupOf.mp hb) b' (Subgroup.mem_subgroupOf.mp hb') u u.2
  · intro b hb
    have hbT : (b : G) ∈ T := hRT (hBR (Subgroup.mem_subgroupOf.mp hb))
    obtain ⟨u, hu, e, he⟩ := C.β_T hbT
    refine ⟨u, hu, e, C.R1_of_core hbT he (hcore b (Subgroup.mem_subgroupOf.mp hb)), ?_⟩
    rw [model_β]
    exact he
  · by_cases hk : ∃ b₁ ∈ B.subgroupOf H, ∃ b₂ ∈ B.subgroupOf H, C.model.β b₁ ≠ 1 ∧
        C.model.β b₂ ≠ 1 ∧ C.model.β b₁ ≠ C.model.β b₂
    · exact Or.inr hk
    left
    push Not at hk
    obtain ⟨b₀, hb₀B, hb₀O⟩ := Set.not_subset.mp hBO
    set b₀' : ↥H := ⟨b₀, hBH hb₀B⟩ with hb₀'
    have hb₀1 : C.model.β b₀' ≠ 1 := fun h => hb₀O (C.β_ker h)
    have hb₀B' : b₀' ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb₀B
    refine ⟨b₀', hb₀B', hb₀1, ?_⟩
    have hidx2 : (B ⊓ pCoreOf 2 H).relIndex B ≤ 2 := by
      have hd : ((B ⊓ pCoreOf 2 H).subgroupOf B).index ∣ 2 := by
        rw [Subgroup.index_dvd_two_iff]
        refine ⟨⟨b₀, hb₀B⟩, fun b => ?_⟩
        by_cases hbO : (b : G) ∈ pCoreOf 2 H
        · exact Or.inr (Subgroup.mem_subgroupOf.mpr ⟨b.2, hbO⟩)
        · left
          have hb1 : C.model.β ⟨b, hBH b.2⟩ ≠ 1 := fun h => hbO (C.β_ker h)
          have heq := hk ⟨b, hBH b.2⟩ (Subgroup.mem_subgroupOf.mpr b.2) b₀' hb₀B' hb1 hb₀1
          have hsq : (b₀' * b₀' : ↥H) = 1 := Subtype.ext (by
            have := hBab.2 b₀ hb₀B
            rwa [pow_two] at this)
          have h1 : C.β (⟨b, hBH b.2⟩ * b₀') = 1 := by
            rw [map_mul, show C.β ⟨b, hBH b.2⟩ = C.β b₀' from heq, ← map_mul, hsq, map_one]
          exact Subgroup.mem_subgroupOf.mpr ⟨B.mul_mem b.2 hb₀B, C.β_ker h1⟩
      exact Nat.le_of_dvd (by norm_num) hd
    have hC4 : (centralizerMod V₁ (conjClosure V H) B).relIndex (conjClosure V H) ≤ 4 :=
      hBidx.trans ((Nat.pow_le_pow_left hidx2 2).trans (by norm_num))
    intro q₀ q₁ q₂ q₃ q₄
    by_contra hall
    push Not at hall
    obtain ⟨u₀, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q₀
    obtain ⟨u₁, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q₁
    obtain ⟨u₂, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q₂
    obtain ⟨u₃, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q₃
    obtain ⟨u₄, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q₄
    set Cm := (centralizerMod V₁ (conjClosure V H) B).subgroupOf (conjClosure V H) with hCm
    have hf1 : ∀ m : ↥(conjClosure V H), m ∈ Cm → C.model.f b₀' (cl m) = 1 := by
      intro m hm
      rw [C.f_cl]
      have h1 := (mem_centralizerMod.mp (Subgroup.mem_subgroupOf.mp hm)).2.2 b₀ hb₀B
      have e : b₀ * (m : G) * b₀⁻¹ * (m : G)⁻¹ = ((m : G) * b₀ * (m : G)⁻¹ * b₀⁻¹)⁻¹ := by group
      rw [cl, A6.A6Mod.secMk_eq_one_iff]
      show (b₀' : G) * (m : G) * (b₀' : G)⁻¹ * (m : G)⁻¹ ∈ V₁
      rw [hb₀', e]
      exact V₁.inv_mem h1
    have hsame : ∀ m m' : ↥(conjClosure V H),
        ((m : ↥(conjClosure V H) ⧸ Cm) = m') → C.model.f b₀' (cl m) = C.model.f b₀' (cl m') := by
      intro m m' hmm
      rw [QuotientGroup.eq] at hmm
      have e : m' = m * (m⁻¹ * m') := by group
      rw [e, show (cl (m * (m⁻¹ * m')) : HSide.Q V H V₁) = cl m * cl (m⁻¹ * m') from
        map_mul _ _ _, Model.f_mul, hf1 _ hmm, mul_one]
    set w : Fin 5 → ↥(conjClosure V H) := ![u₀, u₁, u₂, u₃, u₄] with hw
    have hinj : Function.Injective fun i => ((w i : ↥(conjClosure V H)) :
        ↥(conjClosure V H) ⧸ Cm) := by
      intro i j hij
      have h := hsame _ _ hij
      by_contra hne
      fin_cases i <;> fin_cases j <;> simp [hw] at h hne <;>
        first
        | exact hall.1 h
        | exact hall.2.1 h
        | exact hall.2.2.1 h
        | exact hall.2.2.2.1 h
        | exact hall.2.2.2.2.1 h
        | exact hall.2.2.2.2.2.1 h
        | exact hall.2.2.2.2.2.2.1 h
        | exact hall.2.2.2.2.2.2.2.1 h
        | exact hall.2.2.2.2.2.2.2.2.1 h
        | exact hall.2.2.2.2.2.2.2.2.2 h
        | exact hall.1 h.symm
        | exact hall.2.1 h.symm
        | exact hall.2.2.1 h.symm
        | exact hall.2.2.2.1 h.symm
        | exact hall.2.2.2.2.1 h.symm
        | exact hall.2.2.2.2.2.1 h.symm
        | exact hall.2.2.2.2.2.2.1 h.symm
        | exact hall.2.2.2.2.2.2.2.1 h.symm
        | exact hall.2.2.2.2.2.2.2.2.1 h.symm
        | exact hall.2.2.2.2.2.2.2.2.2 h.symm
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    have : Nat.card (↥(conjClosure V H) ⧸ Cm) =
        (centralizerMod V₁ (conjClosure V H) B).relIndex (conjClosure V H) := rfl
    omega

end HSide

end Levi

theorem lemma14751Levi_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (h48 : Lemma14_7_48) :
    Lemma14751Levi := by
  intro G _ _ T L V H S K hK hHKT hl1 hP π hsurj hker I hV₁I hIU hHI Y V₂ T₀ hV2 hYK _ _ _ _ _ _
    _ hcomm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', hcK', -, -⟩ := h48 G T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    have h1 := cComp_map_mulEquiv (MulAut.conj h) hK
    have e : H.map (MulAut.conj h).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
    rw [e, hcK'] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hpi1 : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ pCoreOf 2 H := fun h => by
    rw [← MonoidHom.mem_ker, hker, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH) hHN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hOT : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le S.hyp hTH
  have hπK : (π.comp (Subgroup.inclusion hKH)).range = alternatingGroup (Fin 8) := by
    set φ := π.comp (Subgroup.inclusion hKH) with hφ
    have hkerφ : φ.ker = CFSG.pCore 2 ↥K := by
      ext k
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hpi1, ← pCoreOf_subgroupOf' K,
        Subgroup.mem_subgroupOf]
      exact mem_pCoreOf_iff_of_mem_cComp hK k.2
    have hcard : Nat.card φ.range = 20160 := by
      obtain ⟨ε⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkerφ).toEquiv,
        ← Nat.card_congr (cStarEquiv K).toEquiv,
        Nat.card_congr (ε.trans Lin.slFourEquivAlt8).toEquiv, Alt8.card_alt8]
    have hnorm : ∀ g ∈ alternatingGroup (Fin 8), ∀ y ∈ φ.range, g * y * g⁻¹ ∈ φ.range := by
      rintro g - _ ⟨k, rfl⟩
      obtain ⟨h, rfl⟩ := hsurj g
      have hk' : (h : G) * k * (h : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hKn h.2) k).mp k.2
      refine ⟨⟨_, hk'⟩, ?_⟩
      show π (Subgroup.inclusion hKH ⟨_, hk'⟩) = π h * π (Subgroup.inclusion hKH k) * (π h)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext rfl)
    rcases Alt8.eq_bot_or_le hnorm with h | h
    · rw [h, Subgroup.card_bot] at hcard
      omega
    · exact (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, Alt8.card_alt8])).symm
  have hπKmem : ∀ k (hk : k ∈ K), π ⟨k, hKH hk⟩ ∈ alternatingGroup (Fin 8) := fun k hk => by
    rw [← hπK]
    exact ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨πK, hπs, hkerK, hD, hPar⟩ :=
    exists_coords51 h1222 h1332 h1334 S hK hKn hl1 hP hsurj hker hπK
  have hcent : ∀ h ∈ H, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → h ∈ pCoreOf 2 H := by
    intro h hh hc
    have hcomm' : π ⟨h, hh⟩ ∈ Subgroup.centralizer
        (alternatingGroup (Fin 8) : Set (Perm (Fin 8))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hπK] at hg
      obtain ⟨k, rfl⟩ := hg
      have h1 : π (⟨h, hh⟩ * Subgroup.inclusion hKH k * ⟨h, hh⟩⁻¹ *
          (Subgroup.inclusion hKH k)⁻¹) = 1 :=
        (hpi1 _).mpr (hOK (hc k k.2))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (by simp), Subgroup.mem_bot] at hcomm'
    exact (hpi1 ⟨h, hh⟩).mp hcomm'
  have hodd : ∃ t ∈ T, ¬ ∃ k ∈ K, ∀ k' ∈ K,
      (k⁻¹ * t) * k' * (k⁻¹ * t)⁻¹ * k'⁻¹ ∈ pCoreOf 2 K := by
    obtain ⟨t₀, ht₀, hodd⟩ := exists_odd_T S hsurj
    refine ⟨t₀, ht₀, ?_⟩
    rintro ⟨k, hk, hkc⟩
    have hm : k⁻¹ * t₀ ∈ H := H.mul_mem (H.inv_mem (hKH hk)) (hTH ht₀)
    have h1 := (hpi1 ⟨_, hm⟩).mpr (hcent _ hm hkc)
    apply hodd
    have e : (⟨t₀, le_sup_right.trans S.hz.1.1 ht₀⟩ : ↥H) = ⟨k, hKH hk⟩ * ⟨_, hm⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, h1, mul_one]
    exact hπKmem k hk
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, c, hz, hz1, ha, haV, hc, hcV⟩ := S14.exists_basis
  obtain ⟨x, hx, -, hxa, hxc⟩ := S14.exists_x hz hz1 ha haV hc hcV
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxl : x ∈ l1 T L V := hl1eq ▸ hx
  have hF := hypF98_of h1222 h1332 h1334 hA37 hA38 hA39 S
  have hUab : IsElemAbelian 2 (conjClosure V H) := hF.F911_3
  have : IsMulCommutative ↥(conjClosure V H) := hUab.1
  have hVU : V ≤ conjClosure V H := le_conjClosure V H
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  have hHV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1
  have hTa : ∀ t ∈ T, t * a * t⁻¹ * a⁻¹ ∈ fsuV1 T V := by
    intro t ht
    have hta : t * a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 ht) a).mp ha
    rcases S14.mem_V2 ha haV hta with h | h
    · exfalso
      apply haV
      exact (Subgroup.mem_normalizer_iff.mp (S14.T_V1 ht) a).mpr h
    · have e : t * a * t⁻¹ * a⁻¹ = a * (t * a * t⁻¹) := by
        have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S14.mul_self_V (hV2.2.1 ha))
        rw [ha1, S14.comm_V ((Subgroup.mem_normalizer_iff.mp (S14.TV ht) a).mp (hV2.2.1 ha))
          (hV2.2.1 ha)]
      rw [e]
      exact h
  have hca : c * a⁻¹ ∉ fsuV1 T V := by
    intro h
    apply hcV
    have := V₂.mul_mem (hV2.1 h) ha
    rwa [inv_mul_cancel_right] at this
  have hO : ∀ h ∈ pCoreOf 2 H, ∀ u ∈ conjClosure V H, h * u * h⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro h hh u hu
    rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at hh
    exact (mem_centralizerMod.mp hh).2.2 u hu
  have C : Levi.HSide T L V H K (fsuV1 T V) πK a c x :=
    { hKH := hKH, hTH := hTH, hKn := hKn, hHN := hHN, hπs := hπs, hkerK := hkerK, hD := hD,
      hPar := hPar, hl1K := hl1, hdec := fun h hh => by
        rw [hHKT] at hh
        exact Levi.exists_mul_of_mem_sup (fun t ht => hKn (hTH ht)) hh
      hcent := hcent, hodd := hodd, hOK := hOK, hOT := hOT, hU := hUab,
      hV₁U := hV₁V.trans hVU, hHV₁ := hHV₁, hO := hO, ha := hVU (hV2.2.1 ha), haV₁ := haV,
      hTa := hTa, hx := hxl, hc := hVU hc, hxa := hxa, hxc := hxc, hca := hca }
  have hV₁V₂ : fsuV1 T V ≤ V₂ := hV2.1
  by_cases hfix : ∀ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ fsuV1 T V
  · have hYV₂ : conjClosure V₂ Y = V₂ := by
      refine le_antisymm (conjClosure_le fun y hy v hv => ?_) (le_conjClosure V₂ Y)
      have hyH : y ∈ H := hKH (hYK hy)
      have hya : y * a * y⁻¹ ∈ V₂ := by
        have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
        rw [e]
        exact V₂.mul_mem (hV₁V₂ (hfix y hy)) ha
      rcases S14.mem_V2 ha haV hv with h | h
      · exact hV₁V₂ ((Subgroup.mem_normalizer_iff.mp (hHV₁ hyH) v).mp h)
      · have e : y * v * y⁻¹ = (y * a * y⁻¹)⁻¹ * (y * (a * v) * y⁻¹) := by group
        rw [e]
        exact V₂.mul_mem (V₂.inv_mem hya)
          (hV₁V₂ ((Subgroup.mem_normalizer_iff.mp (hHV₁ hyH) _).mp h))
    rw [hYV₂]
    have h := relIndex_card_mul hV₁V₂
    rw [S14.card_V1, hV2.2.2.2] at h
    omega
  push Not at hfix
  obtain ⟨y₀, hy₀, hya₀⟩ := hfix
  have hYI : ∀ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ I := by
    intro y hy
    have h1 := hcomm (Subgroup.commutator_mem_commutator ha hy)
    rw [commutatorElement_def] at h1
    have e : y * a * y⁻¹ * a⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact I.inv_mem h1
  have hinf := Setting147.inf_V_eq S h1222 h1332 h1334 hV₁I hIU hHI
  have hxI : c * a⁻¹ ∉ I := fun h => hca (by
    rw [← hinf]
    exact ⟨V.mul_mem hc (V.inv_mem (hV2.2.1 ha)), h⟩)
  have hYP := Levi.HSide.le_stab_of_r2 (C.U_le_map le_sup_right)
    (C.r2_notMem hYK hHI hV₁I hYI hxI)
  have hbad := C.cent_le_T hYK hYP ⟨y₀, hy₀, hya₀⟩
  have hM := C.hyp hbad
  obtain ⟨B, hBR, hQ⟩ := hF.F916_3_aux
  obtain ⟨hBH, hBab, hBO, hBq, hBidx⟩ := hQ
  rw [hl1eq] at hBR
  exact (C.false_of_offender hM hBR hBH hBab hBO hBq hBidx
    (L32A.pCoreOf_le_of_le S.hyp le_sup_right)).elim

end CFSG.Quasithin.H13.L32A.C
