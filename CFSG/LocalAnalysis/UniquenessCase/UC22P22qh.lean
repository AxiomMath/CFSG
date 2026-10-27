module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qf
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qh_isPGroup_pCoreOf (K : Subgroup G) : IsPGroup 2 (pCoreOf 2 K) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype

theorem uc22p22qh_conj_mem_pCoreOf {K : Subgroup G} {k x : G} (hk : k ∈ K) (hx : x ∈ pCoreOf 2 K) :
    k * x * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem y hy ⟨k, hk⟩, rfl⟩

theorem uc22p22qh_le_pCoreOf {K V : Subgroup G} (hVK : V ≤ K) (hV : IsPGroup 2 V)
    (hn : ∀ k ∈ K, ∀ x ∈ V, k * x * k⁻¹ ∈ V) : V ≤ pCoreOf 2 K := by
  have hN : (V.subgroupOf K).Normal := ⟨fun x hx k => hn (k : G) k.2 x hx⟩
  have hQ : IsPGroup 2 (V.subgroupOf K) := hV.comap_subtype
  have hle : V.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, hQ⟩
  intro x hx
  exact ⟨⟨x, hVK hx⟩, hle hx, rfl⟩

theorem uc22p22qh_normalizer_decomp {p : ℕ} [Fact p.Prime] {M P P₀ P₁ : Subgroup G} (hP : IsSylowOf p P M)
    (hcent : P ≤ centralizer (P₁ : Set G)) (hP₀P : P₀ ≤ P)
    (hwc : ∀ g : G, (∀ x ∈ P₀, g⁻¹ * x * g ∈ P) → ∀ x ∈ P₀, g⁻¹ * x * g ∈ P₀) {n : G} (hnM : n ∈ M)
    (hnP₁ : n ∈ normalizer (P₁ : Set G)) :
    ∃ k ∈ M ⊓ centralizer (P₁ : Set G), k⁻¹ * n ∈ normalizer (P₀ : Set G) := by
  set K : Subgroup G := M ⊓ centralizer (P₁ : Set G) with hK
  have hPK : P ≤ K := le_inf hP.le hcent
  have hPKs : IsSylowOf p P K := hP.of_le hPK inf_le_left
  have hnK : ∀ x ∈ K, n * x * n⁻¹ ∈ K := by
    intro x hx
    refine ⟨M.mul_mem (M.mul_mem hnM hx.1) (M.inv_mem hnM), ?_⟩
    exact ((mem_normalizer_iff.1 (uc22p22q_mem_normalizer_centralizer hnP₁) x).1 hx.2)
  set Pn : Subgroup G := P.map (MulAut.conj n).toMonoidHom with hPn
  have hPnK : Pn ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnK x (hPK hx)
  have hPnsyl : IsSylowOf p Pn K := by
    refine isSylowOf_of_card hPnK ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hPKs.card_eq]
  obtain ⟨k, hkK, hk⟩ := hPKs.exists_mem_conj hPnsyl
  refine ⟨k, hkK, ?_⟩
  have hn₀P : ∀ x ∈ P, (k⁻¹ * n) * x * (k⁻¹ * n)⁻¹ ∈ P := by
    intro x hx
    have h1 : n * x * n⁻¹ ∈ Pn := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have h2 := (hk _).1 h1
    have e : (k⁻¹ * n) * x * (k⁻¹ * n)⁻¹ = k⁻¹ * (n * x * n⁻¹) * k := by group
    rw [e]
    exact h2
  have hle : P₀.map (MulAut.conj (k⁻¹ * n)).toMonoidHom ≤ P₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hwc (k⁻¹ * n)⁻¹ (fun y hy => by rw [inv_inv]; exact hn₀P y (hP₀P hy)) x hx
    rw [inv_inv] at h
    exact h
  exact CFSG.Goldschmidt.G310.mem_normalizer_of_map_le hle

theorem uc22p22qh_pCore_le_ctilde (D : Data G) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) :
    pCoreOf 2 D.M ≤ F11.CTilde D.M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hRM : pCoreOf 2 D.M ≤ D.M := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 (pCoreOf 2 D.M) := uc22p22qh_isPGroup_pCoreOf D.M
  have hVR : V ≤ pCoreOf 2 D.M :=
    uc22p22qh_le_pCoreOf hV.2.1 (uc22p22e_isPGroup_of_elem hV.2.2.2)
      (fun k hk x hx => (mem_normalizer_iff.1 (hMV hk) x).1 hx)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.2.2.2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  suffices key : ∀ r ∈ pCoreOf 2 D.M, ∀ v ∈ V, r * v * r⁻¹ * v⁻¹ ∈ V₀ by
    intro r hr
    exact uc22p22q_mem_ctilde.2 ⟨hRM hr, hMV₀ (hRM hr), key r hr⟩
  rcases hH.1 with ⟨hV₀, -, -, hTI₀, hnTI, hgen, -⟩ | ⟨hbot, hW⟩
  ·
    have hne : V ≠ V₀ := fun h => hnTI (by rw [h]; exact hTI₀)
    obtain ⟨v₀, hv₀V, hv₀V₀, hv₀c⟩ := uc22p22q_exists_central_mod (p := 2) hR2 hV₀V hVR
      (fun r hr v hv => (mem_normalizer_iff.1 (hMV (hRM hr)) v).1 hv)
      (fun r hr v hv => (mem_normalizer_iff.1 (hMV₀ (hRM hr)) v).1 hv) hne
    let F : Subgroup G :=
      { carrier := {v | v ∈ V ∧ ∀ r ∈ pCoreOf 2 D.M, r * v * r⁻¹ * v⁻¹ ∈ V₀}
        one_mem' := ⟨V.one_mem, fun r _ => by simp⟩
        mul_mem' := by
          rintro a b ⟨ha, hra⟩ ⟨hb, hrb⟩
          refine ⟨V.mul_mem ha hb, fun r hr => ?_⟩
          have e : r * (a * b) * r⁻¹ * (a * b)⁻¹ =
              (r * a * r⁻¹ * a⁻¹) * (a * (r * b * r⁻¹ * b⁻¹) * a⁻¹) := by group
          rw [e]
          refine V₀.mul_mem (hra r hr) ?_
          have hc : a * (r * b * r⁻¹ * b⁻¹) = (r * b * r⁻¹ * b⁻¹) * a := hVab a ha _ (hV₀V (hrb r hr))
          have : a * (r * b * r⁻¹ * b⁻¹) * a⁻¹ = r * b * r⁻¹ * b⁻¹ := by
            rw [mul_inv_eq_iff_eq_mul]
            exact hc
          rw [this]
          exact hrb r hr
        inv_mem' := by
          rintro a ⟨ha, hra⟩
          refine ⟨V.inv_mem ha, fun r hr => ?_⟩
          have e : r * a⁻¹ * r⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (r * a * r⁻¹ * a⁻¹)⁻¹ * a := by group
          rw [e]
          have hc : a⁻¹ * (r * a * r⁻¹ * a⁻¹)⁻¹ = (r * a * r⁻¹ * a⁻¹)⁻¹ * a⁻¹ :=
            hVab a⁻¹ (V.inv_mem ha) _ (V.inv_mem (hV₀V (hra r hr)))
          have : a⁻¹ * (r * a * r⁻¹ * a⁻¹)⁻¹ * a = (r * a * r⁻¹ * a⁻¹)⁻¹ := by
            rw [hc]
            group
          rw [this]
          exact V₀.inv_mem (hra r hr) }
    have hVF : V ≤ F := by
      rw [← hgen v₀ hv₀V hv₀V₀]
      refine (Subgroup.closure_le F).2 ?_
      rintro _ ⟨m, hm, rfl⟩
      refine ⟨(mem_normalizer_iff.1 (hMV hm) v₀).1 hv₀V, fun r hr => ?_⟩
      have h1 := hv₀c (m⁻¹ * r * m) (by
        have := uc22p22qh_conj_mem_pCoreOf (D.M.inv_mem hm) hr
        simpa using this)
      have h2 := (mem_normalizer_iff.1 (hMV₀ hm) _).1 h1
      have e : m * ((m⁻¹ * r * m) * v₀ * (m⁻¹ * r * m)⁻¹ * v₀⁻¹) * m⁻¹ =
          r * (m * v₀ * m⁻¹) * r⁻¹ * (m * v₀ * m⁻¹)⁻¹ := by group
      rw [e] at h2
      exact h2
    intro r hr v hv
    exact (hVF hv).2 r hr
  ·
    subst hbot
    set C : Subgroup G := D.M ⊓ centralizer (V : Set G) with hC
    set K : Subgroup G := C ⊔ pCoreOf 2 D.M with hK
    have hKM : K ≤ D.M := sup_le inf_le_left hRM
    have hMC : D.M ≤ normalizer (C : Set G) := uc22p22nc_le_normalizer_inf_centralizer hMV
    have hMK : D.M ≤ normalizer (K : Set G) := by
      rw [hK, Subgroup.sup_eq_closure, Subgroup.le_normalizer_closure_iff]
      intro m hm g hg
      rcases hg with hgC | hgR
      · exact Subgroup.subset_closure (Or.inl ((mem_normalizer_iff.1 (hMC hm) g).1 hgC))
      · exact Subgroup.subset_closure (Or.inr (uc22p22qh_conj_mem_pCoreOf hm hgR))
    have hCK : C ≤ K := le_sup_left
    have hRK : pCoreOf 2 D.M ≤ K := le_sup_right
    have hidx : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n := by
      have hsub : (centralizer (V : Set G)).subgroupOf K = C.subgroupOf K := by
        ext x
        simp only [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf]
        exact ⟨fun h => ⟨hKM x.2, h⟩, fun h => h.2⟩
      rw [hsub]
      haveI hCn : (C.subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).2 (hKM.trans hMC)
      have hsup : (pCoreOf 2 D.M).subgroupOf K ⊔ C.subgroupOf K = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hRK hCK, sup_comm, ← hK, Subgroup.subgroupOf_self]
      have h1 := Subgroup.relIndex_sup_right (K := C.subgroupOf K) (H := (pCoreOf 2 D.M).subgroupOf K)
      rw [hsup, Subgroup.relIndex_top_right] at h1
      have hR' : IsPGroup 2 ↥((pCoreOf 2 D.M).subgroupOf K) := hR2.comap_subtype
      obtain ⟨n, hn⟩ := hR'.index ((C.subgroupOf K).subgroupOf ((pCoreOf 2 D.M).subgroupOf K))
      exact ⟨n, h1.trans hn⟩
    have hKV : K ≤ centralizer (V : Set G) := hW.2.2 K hKM hMK hCK hidx
    intro r hr v hv
    have hrc : r ∈ centralizer (V : Set G) := hKV (hRK hr)
    have h1 : v * r = r * v := Subgroup.mem_centralizer_iff.1 hrc v hv
    have : r * v * r⁻¹ * v⁻¹ = 1 := by
      rw [← h1]
      group
    rw [this]
    exact Subgroup.one_mem _

end CFSG.LocalAnalysis.UniquenessCase.UC22
