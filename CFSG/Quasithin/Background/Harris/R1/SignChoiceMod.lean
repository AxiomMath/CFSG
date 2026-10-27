module

public import CFSG.Quasithin.Background.Harris.R1.SignChoice
public import CFSG.Quasithin.Background.Harris.R1.InvolKer
public import CFSG.Quasithin.Recognition.J2RecCzModel

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω) {z : G}

omit [Finite G] in
theorem conj_mem_vBeta (g : ↥(K1 ⊔ S)) {v : G} (hv : v ∈ vBeta K1 L2 S Zs) :
    (g : G) * v * (g : G)⁻¹ ∈ vBeta K1 L2 S Zs :=
  (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S) g.2) v).mp hv

theorem fb_conj (g : ↥(K1 ⊔ S)) {v : G}
    (hv : v ∈ vBeta K1 L2 S Zs) (ω : Ω) :
    fb C ((g : G) * v * (g : G)⁻¹) (permHom C g ω) = fb C v ω := by
  obtain ⟨ε, hε, hg⟩ := FamCtxLemmas.conj_zf_of_mem_sup C g.2 ω
  have hgc : (g : G) ∈ Subgroup.centralizer (Zs : Set G) := C.sup_le_centralizer_Zs g.2
  have hu := conj_mem_vBeta g hv
  have hc : v * C.zf ω * v⁻¹ * (C.zf ω)⁻¹ ∈ Zs := C.U_comm_mem hv (C.zf_mem_U ω)
  have hgcomm : (g : G) * (v * C.zf ω * v⁻¹ * (C.zf ω)⁻¹) * (g : G)⁻¹ =
      v * C.zf ω * v⁻¹ * (C.zf ω)⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hgc _ hc
    rw [← this]; group
  have hεu : ((g : G) * v * (g : G)⁻¹) * ε = ε * ((g : G) * v * (g : G)⁻¹) := C.Zs_central hu hε
  have hεiu : ε⁻¹ * ((g : G) * v * (g : G)⁻¹) = ((g : G) * v * (g : G)⁻¹) * ε⁻¹ := by
    calc ε⁻¹ * ((g : G) * v * (g : G)⁻¹)
        = ε⁻¹ * (((g : G) * v * (g : G)⁻¹) * ε) * ε⁻¹ := by group
      _ = ε⁻¹ * (ε * ((g : G) * v * (g : G)⁻¹)) * ε⁻¹ := by rw [hεu]
      _ = _ := by group
  have hzf : C.zf (permHom C g ω) = (g : G) * C.zf ω * (g : G)⁻¹ * ε⁻¹ := by
    have : (g : G) * C.zf ω * (g : G)⁻¹ = C.zf (permHom C g ω) * ε := hg
    rw [this]; group
  unfold fb
  rw [hzf]
  have e := F112J2.commutator_mul_central (a := (g : G) * v * (g : G)⁻¹)
    (b := (g : G) * C.zf ω * (g : G)⁻¹) (ε := 1) (δ := ε⁻¹) (by simp) (by simp) hεiu
  simp only [mul_one] at e
  rw [e]
  have e2 : (g : G) * v * (g : G)⁻¹ * ((g : G) * C.zf ω * (g : G)⁻¹) *
      ((g : G) * v * (g : G)⁻¹)⁻¹ * ((g : G) * C.zf ω * (g : G)⁻¹)⁻¹ =
      (g : G) * (v * C.zf ω * v⁻¹ * (C.zf ω)⁻¹) * (g : G)⁻¹ := by group
  rw [e2, hgcomm]


theorem fb_of_mem_Zs {x : G} (hx : x ∈ Zs) (ω : Ω) : fb C x ω = 0 := by
  unfold fb
  have h : C.zf ω * x = x * C.zf ω := C.Zs_central (C.zf_mem_U ω) hx
  have : x * C.zf ω * x⁻¹ * (C.zf ω)⁻¹ = 1 := by rw [← h]; group
  rw [this, zbit_one]

theorem mem_Zs_of_fb_eq_zero (hz : z ∈ Zs) (hz1 : z ≠ 1)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {v : G} (hv : v ∈ vBeta K1 L2 S Zs) (h : ∀ ω, fb C v ω = 0) : v ∈ Zs := by
  have hcomm : ∀ ω, v * C.zf ω = C.zf ω * v := by
    intro ω
    have h1 := zbit_eq_zero_iff.mp (h ω)
    calc v * C.zf ω = (v * C.zf ω * v⁻¹ * (C.zf ω)⁻¹) * (C.zf ω * v) := by group
      _ = C.zf ω * v := by rw [h1, one_mul]
  refine hcen v hv fun u hu => ?_
  have hgen : vBeta K1 L2 S Zs ≤ Subgroup.centralizer ({v} : Set G) := by
    refine (C.U_eq_closure hz hz1).le.trans ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl | ⟨ω, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact C.Zs_central hv hz
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm ω
  exact Subgroup.mem_centralizer_iff.mp (hgen hu) v (Set.mem_singleton _)


section Square

variable [Fintype Ω] [DecidableEq Ω]

theorem sq_eq_one_of_lift {σ : Ω → G} (e : Fin 5 ≃ Ω) (hΩ : Fintype.card Ω = 5)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hz : z ∈ Zs) (hz1 : z ≠ 1) (hσ : IsSignChoice C z σ)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) {k t q : G} (hk : k ∈ signStab C σ) (htt : t * t = 1)
    (hq : q ∈ vBeta K1 L2 S Zs) (htq : t = q * k)
    (hπ : ∀ i : Fin 5, C.D.act ⟨k, signStab_le C σ hk⟩ (e i) = e (CFSG.Quasithin.J2Cz.pa i)) :
    k * k = 1 := by
  have hn : 1 < Fintype.card Ω := by omega
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  have hkK : k ∈ K1 := signStab_le C σ hk
  set g : ↥(K1 ⊔ S) := ⟨k, Subgroup.mem_sup_left hkK⟩ with hg
  set pk : Equiv.Perm Ω := C.D.act ⟨k, hkK⟩ with hpk
  have hperm : permHom C g = pk := permHom_K1 C ⟨k, hkK⟩
  have hpkpk : ∀ ω, pk (pk ω) = ω := by
    intro ω
    obtain ⟨i, rfl⟩ := e.surjective ω
    rw [hπ i, hπ]
    congr 1
    revert i; decide
  have hkkZ : k * k ∈ Zs := by
    have hkks : k * k ∈ signStab C σ := (signStab C σ).mul_mem hk hk
    have hact : C.D.act ⟨k * k, signStab_le C σ hkks⟩ = 1 := by
      have hmul : (⟨k * k, signStab_le C σ hkks⟩ : ↥K1) = ⟨k, hkK⟩ * ⟨k, hkK⟩ := rfl
      rw [hmul, map_mul]
      exact Equiv.ext fun ω => by simp [hpkpk, ← hpk]
    have hW := act_eq_one_mem_vBeta C hΩ hL24 hQK hact
    have := signStab_inf_vBeta C hz hz1 hσ hcen hWK
    exact this.le ⟨hW, hkks⟩
  have hqW' : (k * q * k⁻¹) ∈ vBeta K1 L2 S Zs := conj_mem_vBeta g hq
  have h1 : q * (k * q * k⁻¹) = (k * k)⁻¹ := by
    have : (q * k) * (q * k) = 1 := by rw [← htq]; exact htt
    calc q * (k * q * k⁻¹) = (q * k) * (q * k) * (k * k)⁻¹ := by group
      _ = (k * k)⁻¹ := by rw [this, one_mul]
  set g1 : Ω → ZMod 2 := fun ω => fb C q ω with hg1
  have hinv : ∀ ω, g1 (pk ω) = g1 ω := by
    intro ω
    have h2 := fb_mul C hz hz1 hq hqW' (pk ω)
    rw [h1, fb_of_mem_Zs C (Zs.inv_mem hkkZ)] at h2
    have h3 : fb C (k * q * k⁻¹) (pk ω) = g1 ω := by
      have := fb_conj C g hq ω
      rwa [hperm] at this
    rw [h3] at h2
    have key : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
    exact key _ _ h2
  have hsum : ∑ ω, g1 ω = 0 :=
    sum_fb C hz hz1 (by rw [hΩ]; decide) hn hq
  have hsum' : ∑ i : Fin 5, g1 (e i) = 0 := by
    rw [← hsum]; exact Equiv.sum_comp e g1
  set gg : Fin 5 → ZMod 2 := fun i => g1 (e i) with hgg_def
  have hgg : ∀ i, gg (CFSG.Quasithin.J2Cz.pa i) = gg i := fun i => by
    show g1 (e (CFSG.Quasithin.J2Cz.pa i)) = g1 (e i)
    rw [← hπ i]; exact hinv _
  have hgg1 : gg 1 = gg 0 := by
    have := hgg 0
    have h' : CFSG.Quasithin.J2Cz.pa (0 : Fin 5) = 1 := by decide
    rwa [h'] at this
  have hgg3 : gg 3 = gg 2 := by
    have := hgg 2
    have h' : CFSG.Quasithin.J2Cz.pa (2 : Fin 5) = 3 := by decide
    rwa [h'] at this
  have hgg4 : gg 4 = 0 := by
    rw [Fin.sum_univ_five] at hsum'
    have key : ∀ a b c : ZMod 2, a + a + b + b + c = 0 → c = 0 := by decide
    have : gg 0 + gg 1 + gg 2 + gg 3 + gg 4 = 0 := hsum'
    rw [hgg1, hgg3] at this
    exact key _ _ _ this
  set hh : Fin 5 → ZMod 2 := ![gg 0, 0, gg 2, 0, gg 0 + gg 2] with hhh
  set h' : Ω → ZMod 2 := fun ω => hh (e.symm ω) with hh'
  have hsumh : ∑ ω, h' ω = 0 := by
    have : ∑ ω, h' ω = ∑ i : Fin 5, hh i := by
      rw [← Equiv.sum_comp e]; simp [hh']
    rw [this, Fin.sum_univ_five]
    have key : ∀ a b : ZMod 2, a + 0 + b + 0 + (a + b) = 0 := by decide
    exact key _ _
  obtain ⟨v, hvW, hv⟩ := exists_fb_eq C hz hz1 hn h' hsumh
  have htab : ∀ i : Fin 5, hh i + hh (CFSG.Quasithin.J2Cz.pa i) = gg i := by
    have key2 : ∀ a : ZMod 2, a + a = 0 := by decide
    intro i
    fin_cases i
    · have h' : CFSG.Quasithin.J2Cz.pa (0 : Fin 5) = 1 := by decide
      simp [h', hhh]
    · have h' : CFSG.Quasithin.J2Cz.pa (1 : Fin 5) = 0 := by decide
      simp [h', hhh, hgg1]
    · have h' : CFSG.Quasithin.J2Cz.pa (2 : Fin 5) = 3 := by decide
      simp [h', hhh]
    · have h' : CFSG.Quasithin.J2Cz.pa (3 : Fin 5) = 2 := by decide
      simp [h', hhh, hgg3]
    · have h' : CFSG.Quasithin.J2Cz.pa (4 : Fin 5) = 4 := by decide
      simp [h', hhh, hgg4]
      exact key2 _
  have hkey : ∀ ω, h' ω + h' (pk ω) = g1 ω := by
    intro ω
    obtain ⟨i, rfl⟩ := e.surjective ω
    rw [hπ i]
    simp only [hh', Equiv.symm_apply_apply]
    exact htab i
  have hvi : v⁻¹ ∈ vBeta K1 L2 S Zs := (vBeta K1 L2 S Zs).inv_mem hvW
  have hkvk : k * v⁻¹ * k⁻¹ ∈ vBeta K1 L2 S Zs := conj_mem_vBeta g hvi
  have hXW : v * (k * v⁻¹ * k⁻¹) ∈ vBeta K1 L2 S Zs := (vBeta K1 L2 S Zs).mul_mem hvW hkvk
  have hq'W : q⁻¹ * (v * (k * v⁻¹ * k⁻¹)) ∈ vBeta K1 L2 S Zs :=
    (vBeta K1 L2 S Zs).mul_mem ((vBeta K1 L2 S Zs).inv_mem hq) hXW
  have hq'0 : ∀ ω, fb C (q⁻¹ * (v * (k * v⁻¹ * k⁻¹))) ω = 0 := by
    intro ω
    rw [fb_mul C hz hz1 ((vBeta K1 L2 S Zs).inv_mem hq) hXW, fb_inv C hz hz1 hq,
      fb_mul C hz hz1 hvW hkvk]
    have h3 : fb C (k * v⁻¹ * k⁻¹) ω = h' (pk ω) := by
      have := fb_conj C g hvi (pk ω)
      rw [hperm, hpkpk, fb_inv C hz hz1 hvW, hv] at this
      exact this
    rw [h3, hv ω]
    have := hkey ω
    have key : ∀ a b : ZMod 2, a + b = 0 → a + b = 0 := fun _ _ h => h
    have key2 : ∀ a b c : ZMod 2, b + c = a → a + (b + c) = 0 := by decide
    show g1 ω + (h' ω + h' (pk ω)) = 0
    exact key2 _ _ _ this
  set ζ := q⁻¹ * (v * (k * v⁻¹ * k⁻¹)) with hζdef
  have hζ : ζ ∈ Zs := mem_Zs_of_fb_eq_zero C hz hz1 hcen hq'W hq'0
  have hζk : ζ * k = k * ζ := Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hkK) ζ hζ
  have hζv : ζ * v = v * ζ := (C.Zs_central hvW hζ).symm
  have hζζ : ζ * ζ = 1 := C.Zs_sq hζ
  have hqeq : q = v * (k * v⁻¹ * k⁻¹) * ζ⁻¹ := by
    have h2 : q * ζ = v * (k * v⁻¹ * k⁻¹) := by rw [hζdef]; group
    calc q = (q * ζ) * ζ⁻¹ := by group
      _ = _ := by rw [h2]
  have hζi : ζ⁻¹ ∈ Zs := Zs.inv_mem hζ
  have hζik : ζ⁻¹ * k = k * ζ⁻¹ := Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hkK) _ hζi
  have hζiv : ζ⁻¹ * v = v * ζ⁻¹ := (C.Zs_central hvW hζi).symm
  have hζiv' : ζ⁻¹ * v⁻¹ = v⁻¹ * ζ⁻¹ := (C.Zs_central ((vBeta K1 L2 S Zs).inv_mem hvW) hζi).symm
  have hζiζi : ζ⁻¹ * ζ⁻¹ = 1 := C.Zs_sq hζi
  have ht' : t = v * k * v⁻¹ * ζ⁻¹ := by
    rw [htq, hqeq]
    calc v * (k * v⁻¹ * k⁻¹) * ζ⁻¹ * k = v * (k * v⁻¹ * k⁻¹) * (ζ⁻¹ * k) := by group
      _ = v * (k * v⁻¹ * k⁻¹) * (k * ζ⁻¹) := by rw [hζik]
      _ = v * k * v⁻¹ * ζ⁻¹ := by group
  have htt' : t * t = v * (k * k) * v⁻¹ := by
    rw [ht']
    calc v * k * v⁻¹ * ζ⁻¹ * (v * k * v⁻¹ * ζ⁻¹)
        = v * k * (v⁻¹ * (ζ⁻¹ * v)) * k * v⁻¹ * ζ⁻¹ := by group
      _ = v * k * (v⁻¹ * (v * ζ⁻¹)) * k * v⁻¹ * ζ⁻¹ := by rw [hζiv]
      _ = v * (k * ζ⁻¹ * k) * v⁻¹ * ζ⁻¹ := by group
      _ = v * (k * (ζ⁻¹ * k)) * v⁻¹ * ζ⁻¹ := by group
      _ = v * (k * (k * ζ⁻¹)) * v⁻¹ * ζ⁻¹ := by rw [hζik]
      _ = v * (k * k) * (ζ⁻¹ * v⁻¹) * ζ⁻¹ := by group
      _ = v * (k * k) * (v⁻¹ * ζ⁻¹) * ζ⁻¹ := by rw [hζiv']
      _ = v * (k * k) * v⁻¹ * (ζ⁻¹ * ζ⁻¹) := by group
      _ = v * (k * k) * v⁻¹ := by rw [hζiζi, mul_one]
  rw [htt] at htt'
  calc k * k = v⁻¹ * (v * (k * k) * v⁻¹) * v := by group
    _ = 1 := by rw [← htt']; group

end Square

end CFSG.Quasithin.Background.Harris.R1
