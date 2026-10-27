module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

theorem not_le_normalizer_of_lt (F : Frame S m) (hm : 1 ≤ m) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K) :
    ¬ K ≤ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) := by
  intro hle
  have hsub : IsSubnormal (Sec1216Lv.lv L (a₀ * c₀)) (Subgroup.centralizer ({a₀ * c₀} : Set G)) :=
    IsSubnormal.step hlt.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le).mpr hle)
      hK.2.2.1
  have hne : Sec1216Lv.lv L (a₀ * c₀) ≠ ⊥ := by
    obtain ⟨a, haW, ha1⟩ := exists_ne_one_W₁ F hm
    intro hb
    have := S.W₁_le_lv haW
    rw [hb, Subgroup.mem_bot] at this
    exact ha1 this
  exact hK.2.2.2 _ hlt hne (Sec1216Lv.lv_perfect L _) hsub

theorem not_le_normalizer_L_of_lt (F : Frame S m) (hm : 1 ≤ m) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K) : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  apply not_le_normalizer_of_lt F hm hK hlt
  have hKH : K ≤ Subgroup.centralizer ({a₀ * c₀} : Set G) := le_of_mem_cComp hK
  exact Sec1216Lv.le_normalizer_lv hle hKH

variable (S) in
include S in
theorem isSylowTwoOf_Q :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) := by
  have hTM : IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow S.hTL
  have h := A4.isSylowTwoOf_inf_normal hTM inf_le_left fun m hm =>
    Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer hm)
      (normalizer_le_normalizer_centralizer V (S.le_normalizer hm))
  have hQeq : T ⊓ (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) =
      T ⊓ Subgroup.centralizer (V : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr S.hTL]
  rwa [hQeq] at h

variable (S) in
include S in
theorem v_mem_Q : a₀ * c₀ ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
  ⟨Sec1215.le_of_hyp121 S.hyp S.hTL S.v_mem,
    Subgroup.mem_centralizer_iff.mpr fun _ hy => S.comm hy S.v_mem⟩

variable (S) in
include S in
theorem normalizer_Q_le (h331 : Stmt3_3_1) :
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  refine S.normalizer_le_of_characteristic h331 le_rfl (fun hb => S.v_ne_one ?_) ?_
  · have := S.v_mem_Q
    rwa [hb, Subgroup.mem_bot] at this
  · rw [Subgroup.subgroupOf_self]
    infer_instance

variable (S) in
include S in
theorem lv_le_normalizer_Q :
    Sec1216Lv.lv L (a₀ * c₀) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have hQ := setup121Q_holds G T L V V₁ V₂ n S.hyp S.hTL
  rw [← hQ]
  exact (Sec1216Lv.lv_le_L L _).trans
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))

theorem hypC23_of_le (h331 : Stmt3_3_1) (F : Frame S m) (hm : 3 ≤ m) {X R : Subgroup G}
    (hXH : X ≤ Subgroup.centralizer ({a₀ * c₀} : Set G)) (hlvX : Sec1216Lv.lv L (a₀ * c₀) ≤ X)
    (hR : IsSylowTwoOf R (Subgroup.normalizer (L : Set G) ⊓
      Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hRX : R ≤ X) (hQR : T ⊓ Subgroup.centralizer (V : Set G) ≤ R) :
    HypC23 X (T ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G) ⊓ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hR2 : IsPGroup 2 R := hR.2.1
  have hRM : R ≤ M := hR.1.trans inf_le_left
  have hRH : R ≤ H := hR.1.trans inf_le_right
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ M := S.normalizer_Q_le h331
  have hRQ : R ⊓ Subgroup.centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQR inf_le_right)
    exact (A4.isSylowTwoOf_iff_maximal.mp S.isSylowTwoOf_Q).2.2 _ (inf_le_inf_right _ hRM)
      (hR2.to_le inf_le_left) (le_inf hQR inf_le_right)
  have hRNQ : R ≤ Subgroup.normalizer (Q : Set G) := fun r hr => by
    rw [← hRQ]
    exact Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer hr)
      (normalizer_le_normalizer_centralizer V (S.le_normalizer (hRM hr)))
  have hQX : Q ≤ X := hQR.trans hRX
  have hQ1 : Q ≠ ⊥ := fun hb => S.v_ne_one (by
    have := S.v_mem_Q
    rwa [← hQdef, hb, Subgroup.mem_bot] at this)
  have hsq : IsSQTKIn X := IsSQTKIn.mono (sqtkGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple
    S.hyp.nonabelian S.pCoreOf_ne_bot) hXH
  set P := pCoreOf 2 (X ⊓ Subgroup.normalizer (Q : Set G)) with hPdef
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hPX : P ≤ X ⊓ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hPM : P ≤ M ⊓ H :=
    le_inf (hPX.trans (inf_le_right.trans hNQ)) (hPX.trans (inf_le_left.trans hXH))
  have hNP : X ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hPR : P ≤ R := by
    have hRnP : R ≤ Subgroup.normalizer (P : Set G) := (le_inf hRX hRNQ).trans hNP
    have hPR2 : IsPGroup 2 ↥(P ⊔ R) := hP2.to_sup_of_normal_left' hR2 hRnP
    exact le_sup_left.trans ((A4.isSylowTwoOf_iff_maximal.mp hR).2.2 _ (sup_le hPM hR.1) hPR2
      le_sup_right)
  have hlvN : Lv ≤ Subgroup.normalizer (P : Set G) := (le_inf hlvX S.lv_le_normalizer_Q).trans hNP
  have hRlv : R ≤ Subgroup.normalizer (Lv : Set G) := Sec1216Lv.le_normalizer_lv hRM hRH
  have hPV : P ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have hxR := hPR hx
    have hxN : x ∈ Subgroup.normalizer (Lv : Set G) := hRlv hxR
    refine mem_centralizer_V_of_mem_section F hm (hRM hxR) (hRH hxR)
      ⟨Subgroup.mem_top x, hxN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lv hxN,
        fun y hy => ?_⟩
    have hyP : y * x * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hlvN hy) x).mp hx
    have hxy : x * y⁻¹ * x⁻¹ ∈ Lv := (Subgroup.mem_normalizer_iff.mp hxN y⁻¹).mp (Lv.inv_mem hy)
    have h1 : y * x * y⁻¹ * x⁻¹ ∈ P ⊓ Lv := by
      refine ⟨P.mul_mem hyP (P.inv_mem hx), ?_⟩
      have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
      rw [e]
      exact Lv.mul_mem hy hxy
    have hle : P ⊓ Lv ≤ pCoreOf 2 Lv :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun l hl => Sec1216Gen.mem_normalizer_inf (hlvN hl) (Subgroup.le_normalizer hl))
        (hP2.to_le inf_le_left)
    exact hle h1
  have hPQ : P ≤ Q := fun x hx => hRQ ▸ ⟨hPR hx, hPV hx⟩
  have hQP : Q ≤ P := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf hQX Subgroup.le_normalizer) inf_le_right hQ2
  refine ⟨hsq, ⟨hQX, hQ1, le_antisymm hQP hPQ⟩, inf_le_right, ?_, ?_⟩
  · refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hCch => ?_
    exact le_inf (le_inf (inf_le_right.trans (S.normalizer_le_of_characteristic h331 hCQ hC1
      hCch)) (inf_le_left.trans hXH)) inf_le_left
  · refine A4.isSylowTwoOf_mono S.isSylowTwoOf_Q (le_conjClosure Q _) ?_
    refine conjClosure_le fun g hg q hq => ⟨M.mul_mem (M.mul_mem hg.1.1 (S.hTL hq.1))
      (M.inv_mem hg.1.1), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizer V (S.le_normalizer hg.1.1)) q).mp hq.2

variable (S) in
theorem exists_kv_four (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (F : Frame S 3) :
    ∃ K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)), Sec1216Lv.lv L (a₀ * c₀) ≤ K ∧
      Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.hyp.simple
  have hqtke : QTKECore G := qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke
  obtain ⟨R, hR, hRM, -, -⟩ := S.exists_sylow h331 F
  have hRN : R ≤ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) :=
    Sec1216Lv.le_normalizer_lv hRM hR.1
  have hB := lv_mem_lFamily F le_rfl hRN
  obtain ⟨K, hK, hlvK⟩ := Vol2Native.lemma_1_2_4_exists hqtke.1 h37 h39 S.pCoreOf_ne_bot hR
    (Sec1216Lv.lv_le_centralizer L _) hB
  have hn := Vol2Native.lemma_1_2_4_normal hqtke.1 h37 h38 S.pCoreOf_ne_bot hR hB hlvK hK hRN
  exact ⟨K, hK, hlvK, (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK)).mp hn⟩

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
