module

public import CFSG.Quasithin.Background.Harris.KFact2d.Setup
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.Harris.KFact2d.Corr

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_mono {p : ℕ} {E W : Subgroup G} (hW : IsElemAbelian p W) (hle : E ≤ W) :
    IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hW hle

theorem isElemAbelian_map_hom {p : ℕ} {W : Subgroup G} {Y : Type*} [Group Y] (f : G →* Y)
    (hW : IsElemAbelian p W) : IsElemAbelian p (W.map f) := CFSG.Open.IsElemAbelian.map hW _

theorem isElemAbelian_subgroupOf {p : ℕ} {W : Subgroup G} (K : Subgroup G)
    (hW : IsElemAbelian p W) : IsElemAbelian p (W.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hW K

theorem isElemAbelian_star {M H V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsElemAbelian 2 (E2.star M H V) := by
  have hc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hs : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := hV.2 v hv
    rwa [pow_two] at this
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact Ch3E213M.OS.star_comm hc a.1 a.2 b.1 b.2
  · rw [pow_two]
    exact Ch3E213M.OS.star_sq hs x hx

theorem caseI {T N K K0 V : Subgroup G} (hS : StarStmt) (hmp : MinParabolic K T N)
    (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) (hc : CFSG.Quasithin.Gap6R2.E22Case2d K T N K0)
    (hJT : kerIn N K ≤ T) (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hat : ∀ A : Subgroup G, T ≤ A → A ≤ N → ¬ A ≤ Subgroup.normalizer (V : Set G) →
      (∀ B : Subgroup G, T ≤ B → B < A → B ≤ Subgroup.normalizer (V : Set G)) →
      IsElemAbelian 2 (conjClosure V A)) :
    V ≤ pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : T ≤ K := hmp.isSylow.1
  have hNK : N ≤ K := hmp.maximal.1.le
  have hVK : V ≤ K := hVT.trans hTK
  have hJN : kerIn N K ≤ N := kerIn_le
  have hstarN : pre N K (E2.star N K N) = N := pre_star hNK hJN
  have hT2 : IsPGroup 2 T := hmp.isSylow.2.1
  obtain ⟨p, hX⟩ := exists_case2dStar hmp hK0 hKK0 hc
  have hAtom : AtomCond (E2.star N K T) (E2.star N K N) (E2.star N K V) := by
    intro As hTA hAN hnV hcov
    set A := pre N K As with hA
    have hAK : A ≤ K := pre_le As
    have hTA' : T ≤ A := (le_pre_star hTK).trans (pre_mono hTA)
    have hAN' : A ≤ N := by
      have := pre_mono hAN
      rwa [hstarN] at this
    have hstarA : E2.star N K A = As := star_pre As
    have hAnV : ¬ A ≤ Subgroup.normalizer (V : Set G) := by
      intro h
      apply hnV
      rw [← hstarA]
      exact (star_mono h).trans (Ch3E213M.OS.star_le_normalizer (T := Subgroup.normalizer (V : Set G))
        (V := V) le_rfl)
    have hcovA : ∀ B : Subgroup G, T ≤ B → B ≤ A → B = T ∨ B = A := by
      intro B hTB hBA
      have hBK : B ≤ K := hBA.trans hAK
      have hJB : kerIn N K ≤ B := hJT.trans hTB
      have h1 := hcov (E2.star N K B) (star_mono hTB) (hstarA ▸ star_mono hBA)
      rcases h1 with h | h
      · left
        rw [← pre_star hBK hJB, h, pre_star hTK hJT]
      · right
        rw [← pre_star hBK hJB, h]
    have hW := hat A hTA' hAN' hAnV (fun B hTB hBA => by
      rcases hcovA B hTB hBA.le with h | h
      · exact h ▸ hTV
      · exact absurd h (ne_of_lt hBA))
    have hsub : conjClosure (E2.star N K V) As ≤
        (((conjClosure V A).subgroupOf K).map (starMap N K)) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨h', hh', z', hz', rfl⟩
      obtain ⟨hk, rfl⟩ := starMap_surjective N K h'
      obtain ⟨zk, hzk, rfl⟩ := hz'
      have hhkA : (hk : G) ∈ A := mem_pre.mpr ⟨hk.2, by simpa using hh'⟩
      refine ⟨hk * zk * hk⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.subset_closure ⟨(hk : G), hhkA, (zk : G), Subgroup.mem_subgroupOf.mp hzk, by simp⟩)
    exact isElemAbelian_mono (isElemAbelian_map_hom (starMap N K)
      (isElemAbelian_subgroupOf K hW)) hsub
  have hVs := hS (E2.StarQuot N K) (E2.star N K K0) (E2.star N K T) (E2.star N K N)
    (E2.star N K V) p trivial hX (isElemAbelian_star hV) (star_mono hVT)
    (Ch3E213M.OS.star_le_normalizer hTV) hAtom
  set P := pCoreOf 2 (E2.star N K N) with hP
  set R := pre N K P with hR
  have hVR : V ≤ R := (le_pre_star hVK).trans (pre_mono hVs)
  have hPN : P ≤ E2.star N K N := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hRN : R ≤ N := by
    have := pre_mono hPN
    rwa [hstarN] at this
  have hRnorm : N ≤ Subgroup.normalizer (R : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ m ∈ N, ∀ y ∈ R, m * y * m⁻¹ ∈ R := by
      intro m hm y hy
      obtain ⟨hyK, hyP⟩ := mem_pre.mp hy
      refine mem_pre.mpr ⟨K.mul_mem (K.mul_mem (hNK hm) hyK) (K.inv_mem (hNK hm)), ?_⟩
      have hmN : starMap N K ⟨m, hNK hm⟩ ∈ E2.star N K N :=
        ⟨⟨m, hNK hm⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
      have h1 := Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (E2.star N K N) hmN) (starMap N K ⟨y, hyK⟩)
      have h2 := (h1.mp hyP)
      have : (starMap N K ⟨m * y * m⁻¹, K.mul_mem (K.mul_mem (hNK hm) hyK) (K.inv_mem (hNK hm))⟩ :
          E2.StarQuot N K) = starMap N K ⟨m, hNK hm⟩ * starMap N K ⟨y, hyK⟩ *
            (starMap N K ⟨m, hNK hm⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this]
      exact h2
    intro x
    refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
    have := key n⁻¹ (N.inv_mem hn) _ hx
    simpa [mul_assoc] using this
  have hR2 : IsPGroup 2 R := by
    intro g
    obtain ⟨hgK, hgP⟩ := mem_pre.mp g.2
    have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := hPp ⟨_, hgP⟩
    have hk' : (starMap N K ⟨(g : G), hgK⟩) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hker : (⟨(g : G), hgK⟩ : ↥K) ^ 2 ^ k ∈ (starMap N K).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hk'
    rw [ker_starMap] at hker
    have hJ : (g : G) ^ 2 ^ k ∈ kerIn N K := by
      have := Subgroup.mem_subgroupOf.mp hker
      simpa using this
    obtain ⟨j, hj⟩ := hT2 ⟨_, hJT hJ⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  exact hVR.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRN hRnorm hR2)

end CFSG.Quasithin.Background.Harris.KFact2d
