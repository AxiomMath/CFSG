module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Crd
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Five

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

@[expose] def Lem1211HeInsp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G →
    ∀ (H K Y W₁ W₂ : Subgroup G) (m : ℕ) (t : G), pCoreOf 2 H ≠ ⊥ → IsComponentIn K H →
      (m = 3 ∨ m = 4) → Y ≤ K → W₁ ⊔ W₂ ≤ Y → W₁ ⊓ W₂ = ⊥ → IsElemAbelian 2 (W₁ ⊔ W₂) →
      (W₁ ⊔ W₂) ⊓ Subgroup.centralizer (K : Set G) = ⊥ →
      ∀ (C₁ : KGH91.NatCoord Y W₁ m) (C₂ : KGH91.NatCoord Y W₂ m), IsPGroup 2 C₁.ρ.ker →
        (∀ y, C₂.ρ y = slGraphAut m (ZMod 2) (C₁.ρ y)) →
        t ∈ Subgroup.normalizer (K : Set G) → t ∈ Subgroup.normalizer (Y : Set G) →
        (∀ w ∈ W₁, t * w * t⁻¹ ∈ W₂) →
        (m = 3 → ∃ R : Subgroup G, IsSylowTwoOf R K ∧ R ≤ Subgroup.normalizer (Y : Set G)) →
        False

@[expose] def Lem1211HeSchreier : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G → ∀ H K : Subgroup G, pCoreOf 2 H ≠ ⊥ → IsComponentIn K H →
      OutSolvable ↥K

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀}

theorem charTwo_of_lv_le {m : ℕ} (F : Frame S m) (hm : m = 3 ∨ m = 4) (hInsp : Lem1211HeInsp)
    (hlv : ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({a₀ * c₀} : Set G)) →
      Sec1216Lv.lv L (a₀ * c₀) ≤ K)
    (hsyl : m = 3 → ∃ R : Subgroup G,
      IsSylowTwoOf R (Subgroup.centralizer ({a₀ * c₀} : Set G)) ∧
        R ≤ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G)) :
    CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G)) := by
  refine Sec1216Gen.charTwo_of_no_component (fun K hK => ?_) S.oddCoreIn_eq_bot
  have hlvK := hlv K hK
  obtain ⟨t, ht, hta, htc, hs₁, hs₂⟩ := S.exists_swap_pair
  have htv := S.mem_centralizer_of_swap hta htc
  have htN : t ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) :=
    Sec1216Lv.le_normalizer_lv (X := Subgroup.zpowers t) (Subgroup.zpowers_le.mpr ht)
      (Subgroup.zpowers_le.mpr htv) (Subgroup.mem_zpowers t)
  have hinf : S.W₁ ⊓ S.W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ V₁ ⊓ V₂ := ⟨hx.1.1, hx.2.1⟩
    rwa [S.hyp.inf] at h1
  refine hInsp G S.hyp.simple S.hyp.nonabelian S.hyp.qtke _ K _ S.W₁ S.W₂ m t S.pCoreOf_ne_bot hK
    hm hlvK (sup_le S.W₁_le_lv S.W₂_le_lv) hinf (Sec1216Gen.isElemAbelian_of_le S.hVe S.W_le_V)
    (W_inf_centralizer hlvK) (natCoord₁ F) (natCoord₂ F) (isPGroup_ker_natCoord₁ F)
    (natCoord₂_ρ F) (S.mem_normalizer_of_lv_le hK hlvK htv htN) htN
    (fun w hw => conj_mem_W₂ ht htc hs₁ hs₂ hw) fun h3 => ?_
  obtain ⟨R, hR, hRN⟩ := hsyl h3
  exact ⟨R ⊓ K, RankOneRecog.isSylowTwoOf_inf_of_subnormal hR hK.1 hK.2.2,
    inf_le_left.trans hRN⟩

end Setting

end Sec1211Ns

theorem lem1211He_of (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hSch : Lem1211HeSchreier) (hInsp : Lem1211HeInsp) : Lem1211He := by
  intro G _ _ T L V V₁ V₂ n β hyp hTL hβ v hv hns
  obtain ⟨S₀⟩ := KGH91.Setting.nonempty hyp
  obtain ⟨a₀, ha₀, c₀, hc₀, rfl, hac⟩ := hns
  have hP := KGH91.eq_pairing S₀.hn S₀.C₁ S₀.C₂ S₀.dual hβ.1 hβ.2.1 hβ.2.2.2.2
    ⟨a₀, ha₀, c₀, hc₀, by rw [hac]; exact one_ne_zero⟩ a₀ ha₀ c₀ hc₀
  have S : Sec1211Ns.Setting T L V V₁ V₂ n a₀ c₀ :=
    { toSetting := S₀, hTL := hTL, ha₀ := ha₀, hc₀ := hc₀, hns := hP ▸ hac }
  rcases hyp.rank with rfl | rfl
  · obtain ⟨F⟩ := S.nonempty_frame
    have F3 : Sec1211Ns.Frame S 3 := F
    obtain ⟨R, hR, hRM, -, -⟩ := S.exists_sylow h331 F3
    exact Sec1211Ns.Setting.charTwo_of_lv_le F3 (Or.inl rfl) hInsp
      (fun K hK => Sec1211Ns.Setting.lv_le_of_isComponentIn F3 h37 h39 le_rfl hR hRM hK)
      fun _ => ⟨R, hR, Sec1216Lv.le_normalizer_lv hRM hR.1⟩
  · obtain ⟨F⟩ := S.nonempty_frame
    have F4 : Sec1211Ns.Frame S 4 := F
    exact Sec1211Ns.Setting.charTwo_of_lv_le F4 (Or.inr rfl) hInsp
      (fun K hK => Sec1211Ns.Setting.lv_le_of_isComponentIn_five F4 h37 h38 hK
        (hSch G hyp.simple hyp.nonabelian hyp.qtke _ K S.pCoreOf_ne_bot hK))
      fun h => absurd h (by norm_num)

end CFSG.Quasithin.H13
