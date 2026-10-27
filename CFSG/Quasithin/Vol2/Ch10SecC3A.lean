module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Background.A1bReduced
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.LieType.BorelTits

namespace C3

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_conjClosure {K H T V : Subgroup G} (hT : IsSylowIn 2 T K)
    (hF : K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K) (hTH : T ≤ H)
    (hHK : H ≤ K) (hV : IsTwoReducedIn H V) : IsTwoReducedIn K (conjClosure V K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVH, hHV, hVel, hVred⟩ := hV
  have hVK : V ≤ K := hVH.trans hHK
  have hOK : pCoreOf 2 K ≤ T := pCoreOf_le_of_isSylowIn hT
  have hOKH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hOK.trans hTH) (hHK.trans (le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  have hOHC : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) := by
    refine hVred _ (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H) ?_
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  have hOKC : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := hOKH.trans hOHC
  have hVC : V ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact ((Subgroup.mem_centralizer_iff.1 (hOKC hc)) v hv).symm
  have hVO : V ≤ pCoreOf 2 K := fun v hv => hF ⟨hVK hv, hVC hv⟩
  set S := conjClosure V K with hS
  have hSK : S ≤ K := conjClosure_le fun h hh z hz =>
    K.mul_mem (K.mul_mem hh (hVK hz)) (K.inv_mem hh)
  have hSO : ∀ h ∈ K, ∀ z ∈ V, h * z * h⁻¹ ∈ pCoreOf 2 K ∧
      h * z * h⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    intro h hh z hz
    refine ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 K hh) z).1 (hVO hz), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' : h⁻¹ * c * h ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff''.1 (le_normalizer_pCoreOf 2 K hh) c).1 hc
    have := (Subgroup.mem_centralizer_iff.1 (hOKC hc')) z hz
    calc c * (h * z * h⁻¹) = h * ((h⁻¹ * c * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * c * h)) * h⁻¹ := by rw [this]
      _ = h * z * h⁻¹ * c := by group
  have hSO' : ∀ x ∈ S, x ∈ pCoreOf 2 K ∧ x ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    intro x hx
    have : S ≤ pCoreOf 2 K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
      conjClosure_le fun h hh z hz => hSO h hh z hz
    exact this hx
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hSO' y hy).2 x (hSO' x hx).1
  have hSel : IsElemAbelian 2 S := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hScomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
    refine A1b.pow_eq_one_of_mem_closure_of_comm
      (S := {x | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x}) (n := 2) ?_ hScomm hx
    rintro _ ⟨h, hh, z, hz, rfl⟩
    calc (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hVel.2 z hz]; group
  refine ⟨hSK, le_normalizer_conjClosure V K, hSel, ?_⟩
  intro D hDK hKD hD
  have hCnorm : ∀ g ∈ K, ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := fun g hg c hc =>
    A1b.conj_mem_centralizer_of_mem_normalizer (le_normalizer_conjClosure V K hg) hc
  have hNn : ((D ⊓ Subgroup.centralizer (S : Set G)).subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨D.mul_mem (D.mul_mem g.2 hn.1) (D.inv_mem g.2), hCnorm g (hDK g.2) n hn.2⟩
  have hDsyl : IsSylowIn 2 (T ⊓ D) D :=
    hT.inf_normal hDK ((Subgroup.normal_subgroupOf_iff_le_normalizer hDK).2 hKD)
  have hq : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ D ⊓ Subgroup.centralizer (S : Set G) := fun x hx => by
    obtain ⟨k, hk⟩ := hD x hx
    exact ⟨k, D.pow_mem hx _, hk⟩
  have hdec := exists_mul_eq_of_pow_mem hNn hq hDsyl
  have hSV : Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le (le_conjClosure V K)
  have hDH : D ⊓ H ≤ Subgroup.centralizer (V : Set G) := by
    refine hVred (D ⊓ H) inf_le_right ?_ ?_
    · intro h hh
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hKD (hHK hh), Subgroup.le_normalizer hh⟩
    · intro d hd
      obtain ⟨k, hk⟩ := hD d hd.1
      exact ⟨k, hSV hk⟩
  have hDV : D ≤ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨s, hs, n, hn, rfl⟩ := hdec d hd
    exact Subgroup.mul_mem _ (hDH ⟨hs.2, hTH hs.1⟩) (hSV hn.2)
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := (Subgroup.mem_normalizer_iff''.1 (hKD hh) d).1 hd
  have := Subgroup.mem_centralizer_iff.1 (hDV hd') z hz
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [this]
    _ = h * z * h⁻¹ * d := by group

end C3

theorem tmpL6_3_2_2_two_of (h3228 : TmpL6_3_2_2_eight) (h323 : Stmt3_2_3) :
    TmpL6_3_2_2_two := by
  intro G _ _ T L I hfsu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVH, hVred, -⟩ := h3228 G T L I hfsu
  have hred : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVH, hVred⟩
  obtain ⟨⟨hmax, hTM⟩, -⟩ := h323 G T L hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow
    hfsu.maximal hfsu.faithful hfsu.quasisimple
  have hTsyl : IsSylowIn 2 T (fsuM T L) :=
    ⟨hTM, hfsu.sylow.1, fun h => hfsu.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
  have hF : fsuM T L ⊓ Subgroup.centralizer (pCoreOf 2 (fsuM T L) : Set G) ≤
      pCoreOf 2 (fsuM T L) :=
    charTwo_of_inH hfsu.qtke.2.1 (hfsu.sylow.1.toSylow hfsu.sylow.2)
      ⟨hTM, pCoreOf_ne_bot_of_isTwoLocal hmax.1⟩
  have hH : fsuL0 T L ⊔ T ≤ fsuM T L := sup_le Subgroup.le_normalizer hTM
  exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.1
    (C3.isTwoReducedIn_conjClosure hTsyl hF le_sup_right hH hred)

end CFSG.Quasithin.Vol2.Ch10
