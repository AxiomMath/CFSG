module

public import CFSG.Quasithin.H13.A5W1618k

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model B2F E2

local notation "StSL" => Assembly.LowTwoRank.StatedSL

theorem mem_normalizer_centralizer_of_mem_normalizer {G : Type} [Group G] {X : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ h ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      h * c * h⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro h hh c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : h⁻¹ * y * h ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hh) y).mp hy
      simpa using this
    have e1 := hc _ hy'
    calc y * (h * c * h⁻¹) = h * ((h⁻¹ * y * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * y * h)) * h⁻¹ := by rw [e1]
      _ = h * c * h⁻¹ * y := by group
  refine B6.mem_normalizer_of_forall_mem (key g hg) fun c hc => ?_
  have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hg) c hc
  rwa [inv_inv] at this

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem autOn_baum_le_of_natCase {K₀ M : Subgroup G}
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) (hmp : MinParabolic (K₀ ⊔ S.Tv) S.Tv M)
    (hV : IsElemAbelian 2 (conjClosure S.V1 (K₀ ⊔ S.Tv)))
    (hred : IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)))
    (hn : C126.NatCase (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV) :
    autOn (baum S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)) ≤
      autOn (S.Tv ⊓ K₀) (conjClosure S.V1 (K₀ ⊔ S.Tv)) := by
  set H := K₀ ⊔ S.Tv with hHdef
  set V' := conjClosure S.V1 H with hV'def
  have hHN : H ≤ Subgroup.normalizer (V' : Set G) := hred.2.1
  have hK₀N : K₀ ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hHN
  have hTN : S.Tv ≤ Subgroup.normalizer (V' : Set G) := le_sup_right.trans hHN
  have hsylH : IsSylowTwoOf S.Tv H := hmp.isSylow
  obtain ⟨-, I, hfam, hn2⟩ := hn
  obtain ⟨-, hJeq, -, -, -, -, -, -, h2, -⟩ := hfam
  obtain ⟨hsb, hsylJ, -, -⟩ := h2 fun L hL => (hn2 L hL).imp fun n h => h.2
  have hperfL : ∀ L ∈ I, ⁅L, L⁆ = L := by
    intro L hL
    obtain ⟨n, hn, -, F, iF, iFt, hcard, e, -⟩ := hn2 L hL
    have htop := commutator_sl2_eq_top hcard hn
    have hcL : commutator ↥L = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : e y ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [htop]; exact Subgroup.mem_top _
      have hmap : (commutator (Matrix.SpecialLinearGroup (Fin 2) F)).map e.symm.toMonoidHom ≤
          commutator ↥L := by
        rw [commutator_def, Subgroup.map_commutator, commutator_def]
        exact Subgroup.commutator_mono le_top le_top
      have := hmap ⟨e y, hy, rfl⟩
      simpa using this
    exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hcL)
  set X : Subgroup (MulAut (IntMod V' hV)) := ⨆ L ∈ I, L with hX
  have hXp : ⁅X, X⁆ = X := by
    refine le_antisymm (A3.commutator_self_le X) ?_
    refine iSup₂_le fun L hL => ?_
    rw [← hperfL L hL]
    exact Subgroup.commutator_mono (le_iSup₂ (f := fun L (_ : L ∈ I) => L) L hL)
      (le_iSup₂ (f := fun L (_ : L ∈ I) => L) L hL)
  have hXH : X ≤ autOn H V' := by
    rw [← hJeq]
    exact autI_mono hV (B6.thompsonJ_le H)
  have hXK : X ≤ autOn K₀ V' := by
    refine (le_twoResidual_of_perfect hXp hXH).trans ?_
    refine twoResidual_le_of_isTwoQuotient (A4.autOn_mono le_sup_left)
      (CFSG.Quasithin.H13.A5.autOn_le_normalizer_autOn (sup_le Subgroup.le_normalizer hTK₀))
      fun φ hφ => ?_
    obtain ⟨⟨h, hhN⟩, hhH, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨k, hk⟩ := C1.exists_pow_mem_of_mem_sup hsylH.2.1 hTK₀ hhH
    refine ⟨k, Setup.mem_autOn_iff.2 ⟨⟨h, hhN⟩ ^ 2 ^ k, ?_, map_pow _ _ _⟩⟩
    rw [Subgroup.coe_pow]
    exact hk
  have hBK : autOn (baum S.Tv) V' ≤ autOn K₀ V' := by
    have h1 : autI hV (baum S.Tv) ≤ X := by
      rw [hsb, ← hJeq]; exact hsylJ.1
    exact h1.trans hXK
  have hBT : autOn (baum S.Tv) V' ≤ autOn S.Tv V' := A4.autOn_mono inf_le_left
  have hS₀ : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
  have hS₀p : IsSylowTwoOf (autOn (S.Tv ⊓ K₀) V') (autOn K₀ V') :=
    Setup.isSylowTwoOf_autOn hS₀ hK₀N
  have hQ2 : IsPGroup 2 ↥(autOn S.Tv V' ⊓ autOn K₀ V') := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT2 : IsPGroup 2 ↥(autOn S.Tv V') :=
      (hsylH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map (conjAct V')
    exact hT2.to_le inf_le_left
  have heq := hS₀p.eq_of_le (le_inf (A4.autOn_mono inf_le_left) (A4.autOn_mono inf_le_right))
    inf_le_right hQ2
  rw [← heq]
  exact le_inf hBT hBK

theorem exists_mem_normalizer_baum (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = 4) (e : ↥(S.plus K) ≃* ↥(StSL 2 F))
    {K₀ M : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀im : autOn K₀ (S.WK K) = S.plus K)
    (hmp : MinParabolic (K₀ ⊔ S.Tv) S.Tv M)
    (hNQ : K₀ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) ≤ S.Tv)
    (hV : IsElemAbelian 2 (conjClosure S.V1 (K₀ ⊔ S.Tv)))
    (hred : IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)))
    (hn : C126.NatCase (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV) :
    ∃ x ∈ K₀, x ∈ Subgroup.normalizer (baum S.Tv : Set G) ∧
      x ∉ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) ∧
      x ^ 3 ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
  classical
  set W := S.WK K with hWdef
  set H := K₀ ⊔ S.Tv with hHdef
  set V' := conjClosure S.V1 H with hV'def
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have hKW : K ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hsylH : IsSylowTwoOf S.Tv H := hmp.isSylow
  have hS₀ : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
  have hHN : H ≤ Subgroup.normalizer (V' : Set G) := hred.2.1
  have hK₀N : K₀ ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hHN
  have hTN : S.Tv ≤ Subgroup.normalizer (V' : Set G) := le_sup_right.trans hHN
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  set Q₁ := autOn (S.Tv ⊓ K₀) W with hQ₁
  have hQ₁syl : IsSylowTwoOf Q₁ (S.plus K) := hK₀im ▸ Setup.isSylowTwoOf_autOn hS₀ hK₀W
  set π : ↥(StSL 2 F) →* ↥(S.plus K) := e.symm.toMonoidHom with hπ
  obtain ⟨s, -, hsT⟩ := exists_conj_unitriangular (π := π) e.symm.injective e.symm.surjective
    hQ₁syl
  obtain ⟨μ, hμgen⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hμord : orderOf μ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμgen, Nat.card_units, hF4]
  have hμ1 : (μ : F) ≠ 1 := fun h => by
    have : μ = 1 := Units.ext (by rw [h, Units.val_one])
    rw [this, orderOf_one] at hμord
    omega
  set xp : MulAut ↥W := ((π (slOf (s * tor μ * s⁻¹)) : ↥(S.plus K)) : MulAut ↥W) with hxp
  have hxpK : xp ∈ autOn K₀ W := hK₀im ▸ (π (slOf (s * tor μ * s⁻¹))).2
  obtain ⟨⟨x, hxN⟩, hxK₀, hxe⟩ := Setup.mem_autOn_iff.1 hxpK
  have hxpN : xp ∈ Subgroup.normalizer ((Q₁ : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) := hsT μ
  have hcharF' := hcharF
  have hsimp : IsSimpleGroup ↥(S.plus K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo hF4.ge) e
  have hnsolv : ¬ Group.IsSolvable ↥(S.plus K) := fun hs => by
    have : Group.IsSolvable ↥(StSL 2 F) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have hq := S.isQuasisimple_plus h1222 h517 hF hK hT
    exact not_qs_of_le_solvable le_rfl hs hq
  have hsolvW : solvRad K₀ ≤ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
    have hle : solvRad K₀ ≤ K₀ := solvRad_le K₀
    rw [← autOn_eq_bot_iff (hle.trans hK₀W)]
    have hle' : autOn (solvRad K₀) W ≤ S.plus K := hK₀im ▸ A4.autOn_mono hle
    have hnorm : ((autOn (solvRad K₀) W).subgroupOf (S.plus K)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle', ← hK₀im]
      exact CFSG.Quasithin.H13.A5.autOn_le_normalizer_autOn
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp (solvRad_normal K₀))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((autOn (solvRad K₀) W).subgroupOf (S.plus K)) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact Disjoint.eq_bot_of_le h hle'
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      apply hnsolv
      have hs : Group.IsSolvable ↥(solvRad K₀) := solvRad_isSolvable K₀
      have hs2 : Group.IsSolvable ↥((solvRad K₀).subgroupOf
          (Subgroup.normalizer ((W : Subgroup G) : Set G))) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe (hle.trans hK₀W)).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe (hle.trans hK₀W)).injective
      have hs3 : Group.IsSolvable ↥(autOn (solvRad K₀) W) :=
        Group.isSolvable_of_surjective ((conjAct W).subgroupMap_surjective _)
      have heq : autOn (solvRad K₀) W = S.plus K := le_antisymm hle' h
      rw [heq] at hs3
      exact hs3
  have hzV : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hz := S.not_le_centralizer_z_of_plus_eq h1222 h517 hF hK hT hK₀im
  have hCV : ∀ y ∈ K₀, y ∈ Subgroup.centralizer (V' : Set G) → y ∈ S.Tv := by
    intro y hy hyV
    have hsub : IsSubnormal (K₀ ⊓ Subgroup.centralizer (V' : Set G)) K₀ := by
      refine A3.subnormal_of_normal inf_le_left ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro k hk
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, mem_normalizer_centralizer_of_mem_normalizer (hK₀N hk)⟩
    have hlt : K₀ ⊓ Subgroup.centralizer (V' : Set G) < K₀ := by
      refine lt_of_le_of_ne inf_le_left fun h => hz fun k hk => ?_
      have hk' : k ∈ K₀ ⊓ Subgroup.centralizer (V' : Set G) := by rw [h]; exact hk
      have hkV : k ∈ Subgroup.centralizer (V' : Set G) := hk'.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hkV _ hzV).symm
    have h1 := le_solvRad_of_subnormal_lt hK₀ hsub hlt ⟨hy, hyV⟩
    exact hNQ ⟨hy, hsolvW h1⟩
  have hnorm₀ : ∀ y ∈ K₀, ∀ hyN : y ∈ Subgroup.normalizer ((W : Subgroup G) : Set G),
      conjAct W ⟨y, hyN⟩ ∈ Subgroup.normalizer ((Q₁ : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) →
      ∀ s₀ ∈ S.Tv ⊓ K₀, y * s₀ * y⁻¹ ∈ S.Tv ⊓ K₀ := by
    intro y hy hyN hyQ s₀ hs₀
    have hm : y * s₀ * y⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem hy hs₀.2) (K₀.inv_mem hy)
    have hs₀N := hK₀W hs₀.2
    have hmN := hK₀W hm
    have hq : conjAct W ⟨y * s₀ * y⁻¹, hmN⟩ ∈ Q₁ := by
      have e1 : (⟨y * s₀ * y⁻¹, hmN⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G))) =
          ⟨y, hyN⟩ * ⟨s₀, hs₀N⟩ * ⟨y, hyN⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hyQ _).mp
        (Setup.mem_autOn_iff.2 ⟨⟨s₀, hs₀N⟩, hs₀, rfl⟩)
    obtain ⟨⟨s₁, hs₁N⟩, hs₁, hs₁e⟩ := Setup.mem_autOn_iff.1 hq
    have hc : y * s₀ * y⁻¹ * s₁⁻¹ ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
      have h1 : conjAct W (⟨y * s₀ * y⁻¹, hmN⟩ * (⟨s₁, hs₁N⟩ :
          ↥(Subgroup.normalizer ((W : Subgroup G) : Set G)))⁻¹) = 1 := by
        rw [map_mul, map_inv, hs₁e, mul_inv_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have hT1 : y * s₀ * y⁻¹ * s₁⁻¹ ∈ S.Tv :=
      hNQ ⟨K₀.mul_mem hm (K₀.inv_mem hs₁.2), hc⟩
    have e2 : y * s₀ * y⁻¹ = (y * s₀ * y⁻¹ * s₁⁻¹) * s₁ := by group
    refine ⟨?_, hm⟩
    rw [e2]
    exact S.Tv.mul_mem hT1 hs₁.1
  have hbaum := S.autOn_baum_le_of_natCase hTK₀ hmp hV hred hn
  have hconjT : ∀ y ∈ K₀, (∀ s₀ ∈ S.Tv ⊓ K₀, y * s₀ * y⁻¹ ∈ S.Tv ⊓ K₀) →
      ∀ b ∈ baum S.Tv, y * b * y⁻¹ ∈ S.Tv := by
    intro y hy hyS b hb
    have hbT : b ∈ S.Tv := C1GN.baum_le S.Tv hb
    have hbN := hTN hbT
    obtain ⟨⟨s, hsN⟩, hs, hse⟩ :=
      Setup.mem_autOn_iff.1 (hbaum (Setup.mem_autOn_iff.2 ⟨⟨b, hbN⟩, hb, rfl⟩))
    set c := b * s⁻¹ with hc
    have hcV : c ∈ Subgroup.centralizer (V' : Set G) := by
      have h1 : conjAct V' ((⟨b, hbN⟩ : ↥(Subgroup.normalizer (V' : Set G))) *
          (⟨s, hsN⟩ : ↥(Subgroup.normalizer (V' : Set G)))⁻¹) = 1 := by
        rw [map_mul, map_inv, hse, mul_inv_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have hcT : c ∈ S.Tv := S.Tv.mul_mem hbT (S.Tv.inv_mem hs.1)
    have hyV := hK₀N hy
    have hq : c * y * c⁻¹ * y⁻¹ ∈ S.Tv := by
      refine hCV _ ?_ ?_
      · exact K₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTK₀ hcT) y).mp hy) (K₀.inv_mem hy)
      · have h2 : y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V' : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_of_mem_normalizer hyV)
            _).mp (Subgroup.inv_mem _ hcV)
        have e3 : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
        rw [e3]
        exact Subgroup.mul_mem _ hcV h2
    have e4 : y * b * y⁻¹ = (c * y * c⁻¹ * y⁻¹)⁻¹ * c * (y * s * y⁻¹) := by
      rw [hc]; group
    rw [e4]
    exact S.Tv.mul_mem (S.Tv.mul_mem (S.Tv.inv_mem hq) hcT) (hyS s hs).1
  have hxS : ∀ s₀ ∈ S.Tv ⊓ K₀, x * s₀ * x⁻¹ ∈ S.Tv ⊓ K₀ :=
    hnorm₀ x hxK₀ hxN (by rw [hxe]; exact hxpN)
  have hx2N : x ^ 2 ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) := Subgroup.pow_mem _ hxN 2
  have hx2S : ∀ s₀ ∈ S.Tv ⊓ K₀, x ^ 2 * s₀ * (x ^ 2)⁻¹ ∈ S.Tv ⊓ K₀ := by
    intro s₀ hs₀
    have e5 : x ^ 2 * s₀ * (x ^ 2)⁻¹ = x * (x * s₀ * x⁻¹) * x⁻¹ := by rw [pow_two]; group
    rw [e5]
    exact hxS _ (hxS s₀ hs₀)
  have hμ3 : μ ^ 3 = 1 := by rw [← hμord]; exact pow_orderOf_eq_one μ
  have htor1 : tor (1 : Fˣ) = 1 := by
    apply Subtype.ext
    rw [coe_tor, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hx3W : x ^ 3 ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) := by
    have hp : (⟨x, hxN⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G))) ^ 3 =
        ⟨x ^ 3, Subgroup.pow_mem _ hxN 3⟩ := Subtype.ext (by rw [Subgroup.coe_pow])
    refine (A4.conjAct_eq_one_iff (g := ⟨x ^ 3, Subgroup.pow_mem _ hxN 3⟩)).mp ?_
    rw [← hp, map_pow, hxe, hxp, ← Subgroup.coe_pow, ← map_pow, ← map_pow, conj_pow, ← tor_pow,
      hμ3, htor1, mul_one, mul_inv_cancel, map_one, map_one, Subgroup.coe_one]
  have hx3T : x ^ 3 ∈ S.Tv := hNQ ⟨K₀.pow_mem hxK₀ 3, hx3W⟩
  let R : Subgroup G :=
    { carrier := {t | t ∈ S.Tv ∧ x * t * x⁻¹ ∈ S.Tv ∧ x ^ 2 * t * (x ^ 2)⁻¹ ∈ S.Tv}
      one_mem' := ⟨S.Tv.one_mem, by simp [S.Tv.one_mem], by simp [S.Tv.one_mem]⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨S.Tv.mul_mem ha.1 hb.1, ?_, ?_⟩
        · have e6 : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
          rw [e6]; exact S.Tv.mul_mem ha.2.1 hb.2.1
        · have e6 : x ^ 2 * (a * b) * (x ^ 2)⁻¹ =
              (x ^ 2 * a * (x ^ 2)⁻¹) * (x ^ 2 * b * (x ^ 2)⁻¹) := by group
          rw [e6]; exact S.Tv.mul_mem ha.2.2 hb.2.2
      inv_mem' := fun {a} ha => by
        refine ⟨S.Tv.inv_mem ha.1, ?_, ?_⟩
        · have e6 : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
          rw [e6]; exact S.Tv.inv_mem ha.2.1
        · have e6 : x ^ 2 * a⁻¹ * (x ^ 2)⁻¹ = (x ^ 2 * a * (x ^ 2)⁻¹)⁻¹ := by group
          rw [e6]; exact S.Tv.inv_mem ha.2.2 }
  have hRT : R ≤ S.Tv := fun t ht => ht.1
  have hBR : baum S.Tv ≤ R := fun b hb =>
    ⟨C1GN.baum_le S.Tv hb, hconjT x hxK₀ hxS b hb,
      hconjT (x ^ 2) (K₀.pow_mem hxK₀ 2) hx2S b hb⟩
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := by
    have hmap : R.map (MulAut.conj x).toMonoidHom ≤ R := by
      rintro _ ⟨t, ht, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨ht.2.1, ?_, ?_⟩
      · have e7 : x * (x * t * x⁻¹) * x⁻¹ = x ^ 2 * t * (x ^ 2)⁻¹ := by rw [pow_two]; group
        rw [e7]; exact ht.2.2
      · have e7 : x ^ 2 * (x * t * x⁻¹) * (x ^ 2)⁻¹ = x ^ 3 * t * (x ^ 3)⁻¹ := by
          rw [pow_two, pow_three]; group
        rw [e7]
        exact S.Tv.mul_mem (S.Tv.mul_mem hx3T ht.1) (S.Tv.inv_mem hx3T)
    have heq : R.map (MulAut.conj x).toMonoidHom = R := by
      refine Subgroup.eq_of_le_of_card_ge hmap ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  refine ⟨x, hxK₀, ?_, ?_, hx3W⟩
  · rw [baum_eq_of_le hBR hRT]
    exact normalizer_le_normalizer_baum R hxR
  ·
    intro hxc
    have h1 : conjAct W ⟨x, hxN⟩ = 1 := A4.conjAct_eq_one_iff.mpr hxc
    rw [hxe, hxp] at h1
    have h2 : π (slOf (s * tor μ * s⁻¹)) = 1 := Subtype.ext h1
    have h3 : slOf (s * tor μ * s⁻¹) = slOf 1 := by
      rw [map_one]; exact e.symm.injective (by rw [map_one]; exact h2)
    have h4 : s * tor μ * s⁻¹ = 1 :=
      Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h3)
    have h5 : tor μ = 1 := by
      have := congrArg (fun y => s⁻¹ * y * s) h4
      simpa [mul_assoc] using this
    have h6 := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) F =>
      (y : Matrix (Fin 2) (Fin 2) F) 0 0) h5
    simp [coe_tor] at h6
    exact hμ1 (by simp [h6])

end Setting

end CFSG.Quasithin.H13.A5
