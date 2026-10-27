module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NQs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

variable (S) in
include S in
theorem swap_of_mem {r : G} (hr : r ∈ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (h₁ : ∀ a, a ∈ V₁ ↔ r * a * r⁻¹ ∈ V₂) (h₂ : ∀ c, c ∈ V₂ ↔ r * c * r⁻¹ ∈ V₁) :
    r * a₀ * r⁻¹ = c₀ ∧ r * c₀ * r⁻¹ = a₀ := by
  have hv := Subgroup.mem_centralizer_singleton_iff.mp hr
  have e : r * c₀ * r⁻¹ * (r * a₀ * r⁻¹) = a₀ * c₀ := by
    calc r * c₀ * r⁻¹ * (r * a₀ * r⁻¹) = r * (c₀ * a₀) * r⁻¹ := by group
      _ = r * (a₀ * c₀) * r⁻¹ := by rw [S.comm (S.le₂ S.hc₀) (S.le₁ S.ha₀)]
      _ = a₀ * c₀ := by rw [hv, mul_inv_cancel_right]
  obtain ⟨h1, h2⟩ := S.decomp_unique ((h₂ c₀).mp S.hc₀) S.ha₀ ((h₁ a₀).mp S.ha₀) S.hc₀ e
  exact ⟨h2, h1⟩

variable (S) in
include S in
theorem exists_swap_mem_sylow {R : Subgroup G}
    (hR : IsSylowTwoOf R (Subgroup.normalizer (L : Set G) ⊓
      Subgroup.centralizer ({a₀ * c₀} : Set G))) :
    ∃ t ∈ R, t * a₀ * t⁻¹ = c₀ ∧ t * c₀ * t⁻¹ = a₀ := by
  set Mv := Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G) with hMv
  set N₁ : Subgroup G := Mv ⊓ Subgroup.normalizer (V₁ : Set G) with hN₁
  obtain ⟨s, hsM, hsa, hsc, hs₁, hs₂⟩ := S.exists_swap_pair
  have hsMv : s ∈ Mv := ⟨hsM, S.mem_centralizer_of_swap hsa hsc⟩
  have hnot : ∀ g : G, (∀ a, a ∈ V₁ ↔ g * a * g⁻¹ ∈ V₂) →
      g ∉ Subgroup.normalizer (V₁ : Set G) := by
    intro g hg hgN
    have h1 : g * a₀ * g⁻¹ ∈ V₁ ⊓ V₂ :=
      ⟨(Subgroup.mem_normalizer_iff.mp hgN a₀).mp S.ha₀, (hg a₀).mp S.ha₀⟩
    rw [S.hyp.inf, Subgroup.mem_bot] at h1
    apply S.a₀_ne
    calc a₀ = g⁻¹ * (g * a₀ * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hidx : N₁.relIndex Mv = 2 := by
    rw [Subgroup.relIndex]
    refine Subgroup.index_eq_two_iff.mpr ⟨⟨s, hsMv⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases S.fix_or_swap b.2.1 with ⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩
    ·
      refine Or.inr ⟨⟨b.2, hb₁⟩, fun h => hnot ((b : G) * s) (fun a => ?_) h.2⟩
      rw [hs₁ a, show (b : G) * s * a * ((b : G) * s)⁻¹ =
        (b : G) * (s * a * s⁻¹) * (b : G)⁻¹ by group]
      exact Subgroup.mem_normalizer_iff.mp hb₂ _
    ·
      refine Or.inl ⟨⟨Mv.mul_mem b.2 hsMv, Subgroup.mem_normalizer_iff.mpr fun a => ?_⟩,
        fun h => hnot (b : G) hb₁ h.2⟩
      rw [hs₁ a, hb₂, show (b : G) * s * a * ((b : G) * s)⁻¹ =
        (b : G) * (s * a * s⁻¹) * (b : G)⁻¹ by group]
  by_contra hno
  have hRN₁ : R ≤ N₁ := by
    intro r hr
    have hrMv := hR.1 hr
    rcases S.fix_or_swap hrMv.1 with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact ⟨hrMv, h1⟩
    · exact absurd ⟨r, hr, S.swap_of_mem hrMv.2 h1 h2⟩ hno
  have h2 : 2 ∣ (R.subgroupOf Mv).index := by
    have := Subgroup.relIndex_mul_relIndex R N₁ Mv hRN₁ inf_le_left
    rw [hidx] at this
    exact ⟨R.relIndex N₁, show R.relIndex Mv = 2 * R.relIndex N₁ by rw [← this, mul_comm]⟩
  exact hR.2.2 h2

theorem swap_not_inner (F : Frame S m) (hm : 3 ≤ m) {t : G}
    (htM : t ∈ Subgroup.normalizer (L : Set G)) (hta : t * a₀ * t⁻¹ = c₀)
    (htc : t * c₀ * t⁻¹ = a₀) (htN : t ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G)) :
    ¬ ∃ z : Matrix.SpecialLinearGroup (Fin m) (ZMod 2), ∀ x : ↥(Sec1216Lv.lv L (a₀ * c₀)),
      psi F S.lv_le_Xv ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN x).mp x.2⟩ =
        z * psi F S.lv_le_Xv x * z⁻¹ := by
  rintro ⟨z, hz⟩
  have htH := S.mem_centralizer_of_swap hta htc
  obtain ⟨l, rfl⟩ := psi_lv_surjective F z
  have hlY := inv_mul_mem_Y_of_inner F htH htN l hz
  have hlL : (l : G) ∈ L := Sec1216Lv.lv_le_L L _ l.2
  have hC := mem_centralizer_V_of_mem_Y F hm
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hlL)) htM) hlY
  have hc := Subgroup.mem_centralizer_iff.mp hC c₀ (S.le₂ S.hc₀)
  have hl1 : (l : G) * c₀ * (l : G)⁻¹ = c₀ := (S.lv_fix l.2).2
  have htc' : t * c₀ * t⁻¹ = c₀ := by
    calc t * c₀ * t⁻¹ = (l : G) * (((l : G)⁻¹ * t) * c₀ * ((l : G)⁻¹ * t)⁻¹) *
        (l : G)⁻¹ := by group
      _ = (l : G) * c₀ * (l : G)⁻¹ := by
        rw [show ((l : G)⁻¹ * t) * c₀ * ((l : G)⁻¹ * t)⁻¹ = c₀ by rw [← hc]; group]
      _ = c₀ := hl1
  rw [htc] at htc'
  have h1 : c₀ ∈ V₁ ⊓ V₂ := ⟨htc' ▸ S.ha₀, S.hc₀⟩
  rw [S.hyp.inf, Subgroup.mem_bot] at h1
  exact S.c₀_ne h1

theorem isTwoRadicalIn_sup (h331 : Stmt3_3_1) (F : Frame S m) (hm : 3 ≤ m) {K : Subgroup G}
    (hKH : K ≤ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    IsTwoRadicalIn (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G)))
      (T ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hQMv : Q ≤ Subgroup.normalizer (L : Set G) ⊓ H :=
    le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hyp := S.hypC23_of_le h331 F hm le_rfl (Sec1216Lv.lv_le_centralizer L _) hR
    (hR.1.trans inf_le_right) hQR
  obtain ⟨hQH, hQ1, hQeq⟩ := hyp.radical
  have hQKH : Q ≤ K ⊔ Q := le_sup_right
  set P := pCoreOf 2 ((K ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G)) with hPdef
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hPle : P ≤ (K ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hKQH : K ⊔ Q ≤ H := sup_le hKH (hQMv.trans inf_le_right)
  have hNP : H ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer ((K ⊔ Q : Subgroup G) : Set G) :=
      mem_normalizer_sup (hKn hg.1) hg.2
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (Sec1216Gen.mem_normalizer_inf h1 (Subgroup.le_normalizer hg.2))
  have hPQ : P ≤ Q := by
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hPle.trans (inf_le_inf_right _ hKQH)) hNP hP2
    rwa [← hQeq] at h1
  have hQP : Q ≤ P := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf hQKH Subgroup.le_normalizer) inf_le_right hQ2
  exact ⟨hQKH, hQ1, le_antisymm hQP hPQ⟩

theorem le_omegaOneCenterOf (h331 : Stmt3_3_1) (F : Frame S m) (hm : 3 ≤ m) {K : Subgroup G}
    (hchar : CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hKH : K ≤ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    V ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hVQ : V ≤ Q := fun x hx => ⟨Sec1215.le_of_hyp121 S.hyp S.hTL hx,
    Subgroup.mem_centralizer_iff.mpr fun y hy => S.comm hy hx⟩
  have hCV : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer ({a₀ * c₀} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := (inf_le_right.trans hCV).trans hKn
  have hKc : CharTwo K := A4.charTwo_of_normal hKH hKn hchar
  have hXc : CharTwo (K ⊔ Q) := Sec1211Nq.charTwo_sup hQK hQ2 hKc
  have hOQ : pCoreOf 2 (K ⊔ Q) ≤ Q := c2_1_pCore_le (S.isTwoRadicalIn_sup h331 F hm hKH hKn)
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 (K ⊔ Q) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hOQ hy).2 x hx).symm
  have hxO : x ∈ pCoreOf 2 (K ⊔ Q) := hXc ⟨(le_sup_right : Q ≤ K ⊔ Q) (hVQ hx), hxC⟩
  exact Subgroup.subset_closure ⟨⟨hxO, hxC⟩, S.hVe.2 x hx⟩

variable (S) in
theorem exists_pi_autOn (F : Frame S m) {U : Subgroup G} (hWU : S.W₁ ⊔ S.W₂ ≤ U)
    (hLU : Sec1216Lv.lv L (a₀ * c₀) ≤ Subgroup.normalizer (U : Set G)) :
    ∃ π : ↥(autOn (Sec1216Lv.lv L (a₀ * c₀)) U) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      Function.Surjective π ∧ IsPGroup 2 π.ker ∧
        ∀ l, π (InternalSec.autOnHom hLU l) = psi F S.lv_le_Xv l := by
  set ρ := InternalSec.autOnHom hLU with hρdef
  have hρs : Function.Surjective ρ := InternalSec.autOnHom_surjective hLU
  have hle : ρ.ker ≤ (psi F S.lv_le_Xv).ker := by
    intro l hl
    rw [InternalSec.mem_ker_autOnHom] at hl
    rw [MonoidHom.mem_ker, psi_eq_one_iff_gen]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWU) hl
  set π := MonoidHom.liftOfSurjective ρ hρs ⟨psi F S.lv_le_Xv, hle⟩ with hπdef
  have hπ : ∀ l, π (ρ l) = psi F S.lv_le_Xv l := fun l => by simp [hπdef]
  refine ⟨π, fun z => ?_, fun d => ?_, hπ⟩
  · obtain ⟨l, rfl⟩ := psi_lv_surjective F z
    exact ⟨ρ l, hπ l⟩
  · obtain ⟨l, hl⟩ := hρs (d : ↥(autOn (Sec1216Lv.lv L (a₀ * c₀)) U))
    have h1 : psi F S.lv_le_Xv l = 1 := by
      rw [← hπ, hl]
      exact d.2
    obtain ⟨a, ha⟩ := isPGroup_ker_psi_lv F ⟨l, h1⟩
    refine ⟨a, Subtype.ext ?_⟩
    have h2 : l ^ 2 ^ a = 1 := congrArg Subtype.val ha
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hl, ← map_pow, h2, map_one]

omit [Finite G] in
theorem conjAct_mem_normalizer_autOn {U A : Subgroup G} (g : ↥(Subgroup.normalizer (U : Set G)))
    (hg : (g : G) ∈ Subgroup.normalizer (A : Set G)) :
    conjAct U g ∈ Subgroup.normalizer (autOn A U : Set (MulAut ↥U)) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn g hg

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
