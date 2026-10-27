module

public import CFSG.Quasithin.H13.A5W1620L32a
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.H13.A5Z1367i

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Lv_le_of_not_commute_red (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hK₀W : autOn K₀ (S.WK K) = S.plus K) (hLvK : S.Lv ≤ Subgroup.normalizer (K₀ : Set G))
    {F : Type} [Field F] [Finite F] (hF2 : Nat.card F = 2)
    (e : ↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hne : ∃ l ∈ S.Lv, ∃ k ∈ K₀, ∃ w ∈ S.WK K,
      k * (l * w * l⁻¹) * k⁻¹ ≠ l * (k * w * k⁻¹) * l⁻¹) :
    S.Lv ≤ K₀ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have hHW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKW : K₀ ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    hK₀K.trans ((le_sup_left.trans le_sup_left).trans hHW)
  have hLvW : S.Lv ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans hHW
  set W := S.WK K with hWdef
  set Kp := S.plus K with hKp
  have hplus : ∀ k (hk : k ∈ K₀), conjAct W ⟨k, hKW hk⟩ ∈ Kp := fun k hk => by
    rw [← hK₀W]
    exact Setup.mem_autOn_iff.2 ⟨⟨k, hKW hk⟩, hk, rfl⟩
  have hmemKp : ∀ x ∈ Kp, ∃ g : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G)),
      (g : G) ∈ K₀ ∧ conjAct W g = x := fun x hx => by
    rw [← hK₀W] at hx
    exact Setup.mem_autOn_iff.1 hx
  have hconj : ∀ (g k : G) (hg : g ∈ Subgroup.normalizer ((W : Subgroup G) : Set G))
      (hk : k ∈ Subgroup.normalizer ((W : Subgroup G) : Set G)),
      conjAct W ⟨g, hg⟩ * conjAct W ⟨k, hk⟩ * (conjAct W ⟨g, hg⟩)⁻¹ =
        conjAct W ⟨g * k * g⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hk)
          (Subgroup.inv_mem _ hg)⟩ := by
    intro g k hg hk
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hnorm : ∀ g (hg : g ∈ S.Lv),
      conjAct W ⟨g, hLvW hg⟩ ∈ Subgroup.normalizer (Kp : Set (MulAut ↥W)) := by
    intro g hg
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · obtain ⟨k, hkK, rfl⟩ := hmemKp x hx
      rw [hconj]
      exact hplus _ ((Subgroup.mem_normalizer_iff.mp (hLvK hg) k).mp hkK)
    · obtain ⟨k, hkK, rfl⟩ := hmemKp x hx
      have hgi : g⁻¹ ∈ S.Lv := S.Lv.inv_mem hg
      have e1 : (conjAct W ⟨g, hLvW hg⟩)⁻¹ = conjAct W ⟨g⁻¹, hLvW hgi⟩ := by
        rw [← map_inv]
        rfl
      have e2 : conjAct W ⟨g, hLvW hg⟩ = (conjAct W ⟨g⁻¹, hLvW hgi⟩)⁻¹ := by
        rw [← map_inv]
        congr 1
        exact Subtype.ext (inv_inv g).symm
      rw [e1, e2, hconj]
      exact hplus _ ((Subgroup.mem_normalizer_iff.mp (hLvK hgi) k).mp hkK)
  obtain ⟨y₀, hyLv, hyodd, hyρ⟩ := S.exists_Lv_c234_odd
  set y : G := (y₀ : G) with hy
  have hy3 : y ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (S.orderOf_dvd_three_of_Lv hyLv hyodd)
  have hyQ : y ∉ S.LvQ := by
    intro h
    obtain ⟨hV, -, hρ1⟩ := S.mem_LvQ.1 h
    have h1 : S.frame.ρ y₀ = 1 := hρ1
    rcases hyρ with h' | h' <;> rw [h'] at h1 <;> exact absurd h1 (by decide)
  set yP := conjAct W ⟨y, hLvW hyLv⟩ with hyP
  have hyPN := hnorm y hyLv
  set α : MulAut ↥Kp := conjAct Kp ⟨yP, hyPN⟩ with hα
  have hyP3 : yP ^ 3 = 1 := by
    rw [hyP, ← map_pow]
    have h2 : (⟨y, hLvW hyLv⟩ : ↥(Subgroup.normalizer ((W : Subgroup G) : Set G))) ^ 3 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hy3)
    rw [h2, map_one]
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have h1 : (⟨yP, hyPN⟩ : ↥(Subgroup.normalizer (Kp : Set (MulAut ↥W)))) ^ 3 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hyP3)
    rw [h1, map_one]
  have hαx : ∀ x : ↥Kp, ((α x : ↥Kp) : MulAut ↥W) = yP * x * yP⁻¹ := fun x =>
    Setup.coe_conjAct_apply _ x
  obtain ⟨e₀⟩ := L32.nonempty_equiv_GL32 hF2
  set E : ↥Kp ≃* CFSG.QuasithinUnique.Setup.Family.GL32 := e.trans e₀ with hE
  obtain ⟨c, hc⟩ := L32.exists_conj_of_pow_three E α hα3
  have hαc : ∀ x : ↥Kp, α x = c * x * c⁻¹ := fun x => by rw [hc]; rfl
  have hc3 : c ^ 3 = 1 := by
    have h1 : MulAut.conj (c ^ 3) = 1 := by rw [map_pow, ← hc, hα3]
    have hcen : c ^ 3 ∈ Subgroup.center ↥Kp := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut ↥Kp => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * c ^ 3 = c ^ 3 * g * (c ^ 3)⁻¹ * c ^ 3 := by rw [h2]
        _ = c ^ 3 * g := by group
    have hEc : E (c ^ 3) ∈ Subgroup.center CFSG.QuasithinUnique.Setup.Family.GL32 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := E.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hcen) x]
    rw [CFSG.QuasithinUnique.Setup.Family.center_GL32, Subgroup.mem_bot] at hEc
    exact E.injective (hEc.trans (map_one E).symm)
  by_cases hc1 : c = 1
  ·
    exfalso
    have hyC : ∀ x ∈ Kp, yP * x * yP⁻¹ = x := by
      intro x hx
      have h1 := hαx ⟨x, hx⟩
      rw [hαc, hc1] at h1
      simp only [one_mul, inv_one, mul_one] at h1
      exact h1.symm
    set N : Subgroup G :=
      ((Subgroup.centralizer (Kp : Set (MulAut ↥W))).comap (conjAct W)).map
        (Subgroup.normalizer ((W : Subgroup G) : Set G)).subtype with hN
    have hmemN : ∀ g (hg : g ∈ Subgroup.normalizer ((W : Subgroup G) : Set G)),
        (∀ x ∈ Kp, conjAct W ⟨g, hg⟩ * x * (conjAct W ⟨g, hg⟩)⁻¹ = x) → g ∈ N := by
      intro g hg hgx
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * conjAct W ⟨g, hg⟩ =
          conjAct W ⟨g, hg⟩ * x * (conjAct W ⟨g, hg⟩)⁻¹ * conjAct W ⟨g, hg⟩ := by
            rw [hgx x hx]
        _ = conjAct W ⟨g, hg⟩ * x := by group
    have hNmem : ∀ g ∈ N, ∃ hg : g ∈ Subgroup.normalizer ((W : Subgroup G) : Set G),
        ∀ x ∈ Kp, conjAct W ⟨g, hg⟩ * x * (conjAct W ⟨g, hg⟩)⁻¹ = x := by
      rintro g ⟨g', hg', rfl⟩
      refine ⟨g'.2, fun x hx => ?_⟩
      have hc' := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hg')) x hx
      show conjAct W g' * x * (conjAct W g')⁻¹ = x
      rw [← hc']
      group
    have key : ∀ q ∈ S.LvQ, ∀ g ∈ N, q * g * q⁻¹ ∈ N := by
      intro q hq g hg
      have hqLv : q ∈ S.Lv := S.LvQ_le_Lv hq
      obtain ⟨hgW, hgx⟩ := hNmem g hg
      have hqgW : q * g * q⁻¹ ∈ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLvW hqLv) hgW) (Subgroup.inv_mem _ (hLvW hqLv))
      refine hmemN _ hqgW fun x hx => ?_
      have e1 : conjAct W ⟨q * g * q⁻¹, hqgW⟩ =
          conjAct W ⟨q, hLvW hqLv⟩ * conjAct W ⟨g, hgW⟩ * (conjAct W ⟨q, hLvW hqLv⟩)⁻¹ :=
        (hconj q g (hLvW hqLv) hgW).symm
      have hx' : (conjAct W ⟨q, hLvW hqLv⟩)⁻¹ * x * conjAct W ⟨q, hLvW hqLv⟩ ∈ Kp := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hnorm q hqLv)) x).mp hx
        simpa using h1
      have h2 := hgx _ hx'
      rw [e1]
      calc conjAct W ⟨q, hLvW hqLv⟩ * conjAct W ⟨g, hgW⟩ * (conjAct W ⟨q, hLvW hqLv⟩)⁻¹ * x *
            (conjAct W ⟨q, hLvW hqLv⟩ * conjAct W ⟨g, hgW⟩ * (conjAct W ⟨q, hLvW hqLv⟩)⁻¹)⁻¹ =
          conjAct W ⟨q, hLvW hqLv⟩ * (conjAct W ⟨g, hgW⟩ *
            ((conjAct W ⟨q, hLvW hqLv⟩)⁻¹ * x * conjAct W ⟨q, hLvW hqLv⟩) *
            (conjAct W ⟨g, hgW⟩)⁻¹) * (conjAct W ⟨q, hLvW hqLv⟩)⁻¹ := by group
        _ = x := by rw [h2]; group
    have hQN : S.LvQ ≤ Subgroup.normalizer (N : Set G) := by
      intro q hq
      refine B6.mem_normalizer_of_forall_mem (fun g hg => key q hq g hg) fun g hg => ?_
      have h1 := key q⁻¹ (S.LvQ.inv_mem hq) g hg
      rwa [inv_inv] at h1
    have hyN : y ∈ N := hmemN y (hLvW hyLv) hyC
    have hLvN := S.Lv_le_of_mem hQN hyN hyLv hyQ
    obtain ⟨l, hl, k, hk, w, hw, hne'⟩ := hne
    obtain ⟨hlW, hlx⟩ := hNmem l (hLvN hl)
    have h1 := hlx _ (hplus k hk)
    have h2 : conjAct W ⟨l, hlW⟩ * conjAct W ⟨k, hKW hk⟩ =
        conjAct W ⟨k, hKW hk⟩ * conjAct W ⟨l, hlW⟩ := by
      calc conjAct W ⟨l, hlW⟩ * conjAct W ⟨k, hKW hk⟩ =
          (conjAct W ⟨l, hlW⟩ * conjAct W ⟨k, hKW hk⟩ * (conjAct W ⟨l, hlW⟩)⁻¹) *
            conjAct W ⟨l, hlW⟩ := by group
        _ = conjAct W ⟨k, hKW hk⟩ * conjAct W ⟨l, hlW⟩ := by rw [h1]
    have h3 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h2
    simp only [MulAut.mul_apply, Setup.coe_conjAct_apply] at h3
    exact hne' h3.symm
  · have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    by_cases hall : ∀ t ∈ S.Tv ⊓ K₀, y * t * y⁻¹ * t⁻¹ ∈ S.LvQ
    · exfalso
      have hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₀K.trans hK.1
      have hsylH : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
        C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) le_sup_right
          (sup_le hK₀G S.Tv_le_Gv)
      have hsyl : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
        A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
      have hTQ : S.Tv ⊓ K₀ ≤ Subgroup.normalizer (S.LvQ : Set G) :=
        inf_le_left.trans S.Tv_le_normalizer_LvQ
      have hyT := Setting.conj_mem_of_comm_mem hsyl S.isPGroup_LvQ hTQ (hLvK hyLv) hall
      let f : ↥K₀ →* ↥Kp :=
        ((conjAct W).comp (Subgroup.inclusion hKW)).codRestrict Kp fun k => hplus k k.2
      have hf : Function.Surjective f := by
        rintro ⟨x, hx⟩
        obtain ⟨g, hgK, rfl⟩ := hmemKp x hx
        exact ⟨⟨g, hgK⟩, rfl⟩
      set B' : Subgroup ↥K₀ := (S.Tv ⊓ K₀).subgroupOf K₀ with hB'
      have hB'2 : IsPGroup 2 ↥B' :=
        hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
      have hB'i : ¬ 2 ∣ B'.index := hsyl.2.2
      set P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
        (B'.map f).map e.toMonoidHom with hP
      have hP2 : IsPGroup 2 ↥P := (hB'2.map f).map _
      have hPi : ¬ 2 ∣ P.index := fun h => hB'i (h.trans
        ((Subgroup.index_map_dvd _ e.surjective).trans (Subgroup.index_map_dvd _ hf)))
      have hfc : ∀ t (ht : t ∈ S.Tv ⊓ K₀),
          c * f ⟨t, ht.2⟩ * c⁻¹ = f ⟨y * t * y⁻¹, (hyT t ht).2⟩ := by
        intro t ht
        rw [← hαc]
        apply Subtype.ext
        rw [hαx]
        show yP * conjAct W ⟨t, hKW ht.2⟩ * yP⁻¹ = conjAct W ⟨y * t * y⁻¹, hKW (hyT t ht).2⟩
        rw [hyP, hconj]
      have hcP : e c ∈ Subgroup.normalizer (P : Set ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
        refine B6.mem_normalizer_of_forall_mem ?_ ?_
        · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
          have hb' : (b : G) ∈ S.Tv ⊓ K₀ := Subgroup.mem_subgroupOf.mp hb
          refine ⟨_, ⟨⟨y * b * y⁻¹, (hyT b hb').2⟩, Subgroup.mem_subgroupOf.mpr (hyT b hb'),
            rfl⟩, ?_⟩
          show e (f ⟨y * b * y⁻¹, (hyT b hb').2⟩) = e c * e (f b) * (e c)⁻¹
          rw [← hfc b hb', map_mul, map_mul, map_inv]
        · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
          have hb' : (b : G) ∈ S.Tv ⊓ K₀ := Subgroup.mem_subgroupOf.mp hb
          obtain ⟨t, ht, htb⟩ : ∃ t ∈ S.Tv ⊓ K₀, y * t * y⁻¹ = b := by
            have hinj : Function.Injective fun t : ↥(S.Tv ⊓ K₀) =>
                (⟨y * t * y⁻¹, hyT t t.2⟩ : ↥(S.Tv ⊓ K₀)) := by
              intro t₁ t₂ h12
              have h' := congrArg Subtype.val h12
              exact Subtype.ext (by simpa using h')
            obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj ⟨b, hb'⟩
            exact ⟨t, t.2, congrArg Subtype.val ht⟩
          refine ⟨_, ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, ?_⟩
          have hbt : b = ⟨y * t * y⁻¹, (hyT t ht).2⟩ := Subtype.ext htb.symm
          show e (f ⟨t, ht.2⟩) = (e c)⁻¹ * e (f b) * (e c)⁻¹⁻¹
          rw [hbt, ← hfc t ht, map_mul, map_mul, map_inv, inv_inv]
          group
      have hno := factSylowNormSL3 F 1 odd_one (by rw [pow_one]; exact hF2) P hP2 hPi (e c) hcP
      rw [MulEquiv.orderOf_eq, hco] at hno
      exact hno rfl
    ·
      push Not at hall
      obtain ⟨t, ht, htQ⟩ := hall
      have hgK : y * t * y⁻¹ * t⁻¹ ∈ K₀ :=
        K₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLvK hyLv) t).mp ht.2) (K₀.inv_mem ht.2)
      have hgLv : y * t * y⁻¹ * t⁻¹ ∈ S.Lv := by
        have h1 : t * y⁻¹ * t⁻¹ ∈ S.Lv :=
          (Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv ht.1) _).mp (S.Lv.inv_mem hyLv)
        have e1 : y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
        rw [e1]
        exact S.Lv.mul_mem hyLv h1
      exact S.Lv_le_of_mem (fun q hq => hLvK (S.LvQ_le_Lv hq)) hgK hgLv htQ

end Setting

end CFSG.Quasithin.H13.A5
