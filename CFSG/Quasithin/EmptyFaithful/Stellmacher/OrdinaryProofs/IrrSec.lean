module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42IrrDef
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase
public import CFSG.Quasithin.EmptyFaithful.SzF53MNatL2

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G]

theorem mem_normalizer_bot (k : G) : k ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem isSec_bot {X V : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) : IsSec X ⊥ V where
  le := bot_le
  normN := hXN
  normL := fun k _ => mem_normalizer_bot k
  comm := fun x hx y hy => by
    have := hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    have h2 : x * y = y * x := congrArg Subtype.val this
    rw [Subgroup.mem_bot, h2]
    group
  sq := fun x hx => by rw [Subgroup.mem_bot]; exact hV.2 x hx

theorem cSecIn_bot (X V : Subgroup G) :
    cSecIn X ⊥ V = X ⊓ Subgroup.centralizer (V : Set G) := by
  ext f
  rw [mem_cSecIn_iff (fun k _ => mem_normalizer_bot k), Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have h1 := h x hx
    rw [Subgroup.mem_bot] at h1
    have e : f * x = (f * x * f⁻¹ * x⁻¹) * (x * f) := by group
    rw [h1, one_mul] at e
    exact e.symm
  · rw [Subgroup.mem_bot]
    have e : f * x = x * f := (h x hx).symm
    rw [e]
    group

theorem fixSecIn_zpowers_bot (V : Subgroup G) (a : G) :
    fixSecIn (Subgroup.zpowers a) ⊥ V = V ⊓ Subgroup.centralizer ({a} : Set G) := by
  ext x
  rw [mem_fixSecIn_zpowers_iff (fun k _ => mem_normalizer_bot k) (mem_normalizer_bot a),
    Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h => ?_⟩
  · rw [Subgroup.mem_bot] at h
    rw [Set.mem_singleton_iff.mp hy]
    have e : a * x = (a * x * a⁻¹ * x⁻¹) * (x * a) := by group
    rw [h, one_mul] at e
    exact e
  · rw [Subgroup.mem_bot]
    have e : a * x = x * a := h a rfl
    rw [e]
    group

theorem secData_secModule [Finite G] {H L N : Subgroup G} (hs : IsSec H L N) {n : ℕ}
    (θ : ↥H →* Perm (Fin n)) (hθ : Function.Surjective θ)
    (hk : θ.ker ≤ (cSecIn H L N).subgroupOf H) [(L.subgroupOf N).Normal] :
    SecData (secModule hs θ hθ hk) H L N θ (MonoidHom.id hs.W) where
  surj := Function.surjective_id
  inj := Function.injective_id
  equiv := fun k u x hux => by
    refine ⟨hs.conj_mem_N k x, ?_⟩
    have h1 : u = hs.proj x := hux
    subst h1
    exact secModule_act_proj hs θ hθ hk k x

theorem irrSec_aux [Finite G] {X V T : Subgroup G} (hs : IsSec X ⊥ V)
    (hCc : cSecIn X ⊥ V = pCoreOf 2 X) (hVc : V ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hgen : ∀ U : Subgroup G, U ≤ V → X ≤ Subgroup.normalizer (U : Set G) →
      V ⊓ Subgroup.centralizer (T : Set G) ≤ U → U = V)
    (Ψ : ↥X →* Perm (Fin 5)) (hΨs : Function.Surjective Ψ)
    (hΨk : Ψ.ker = (cSecIn X ⊥ V).subgroupOf X) (hPS : (T.subgroupOf X).map Ψ = S5Syl)
    {a : G} (ha : a ∈ oTwoRes X ⊔ pCoreOf 2 X) (haN : a ∉ pCoreOf 2 X)
    (ha23 : a ^ 2 ∈ pCoreOf 2 X ∨ a ^ 3 ∈ pCoreOf 2 X)
    (hidx : (V ⊓ Subgroup.centralizer ({a} : Set G)).relIndex V ≤ 8) :
    IsOrthSec X ⊥ V ∨ IsNatSec X ⊥ V := by
  have := hs.normal_subgroupOf
  set M := secModule hs Ψ hΨs hΨk.le with hM
  have hsd : SecData M X ⊥ V Ψ (MonoidHom.id hs.W) := secData_secModule hs Ψ hΨs hΨk.le
  have hnt : ∃ w : M.W, w ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨k, hk⟩ := hΨs (Equiv.swap (0 : Fin 5) 1)
    have h1 : M.act (Ψ k) = 1 := MulEquiv.ext fun w => (hall _).trans (hall _).symm
    have h2 := (secModule_act_eq_one_iff hs Ψ hΨs hΨk.le k).mp h1
    have h3 : Ψ k = 1 := hΨk.ge (Subgroup.mem_subgroupOf.mpr h2)
    rw [hk] at h3
    exact absurd h3 (by decide)
  have hfix : fixW M ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := hs.proj_surjective w
    refine Subgroup.mem_bot.mpr ((hs.proj_eq_one_iff v).mpr ?_)
    rw [← hVc]
    refine ⟨v.2, ?_⟩
    show (v : G) ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h0 := hw (Ψ ⟨k, hk⟩) (Subgroup.mem_top _)
    rw [secModule_act_proj hs Ψ hΨs hΨk.le] at h0
    have h1 : hs.proj (hs.conjN ⟨k, hk⟩ v) = hs.proj v := h0
    have h2 : (k * (v : G) * k⁻¹)⁻¹ * (v : G) = 1 :=
      Subgroup.mem_bot.mp ((hs.proj_eq_proj_iff _ _).mp h1)
    rw [inv_mul_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm.symm
  have hgen' : ∀ U : Subgroup M.W, IsInvSub M ⊤ U → fixW M S5Syl ≤ U → U = ⊤ := by
    intro U hU hfixU
    set U' : Subgroup G := (U.comap hs.proj).map V.subtype with hU'
    have hU'V : U' ≤ V := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hmem : ∀ x : G, x ∈ U' ↔ ∃ hx : x ∈ V, hs.proj ⟨x, hx⟩ ∈ U := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hx, h⟩
        exact ⟨⟨x, hx⟩, h, rfl⟩
    have hinv : ∀ k ∈ X, ∀ x ∈ U', k * x * k⁻¹ ∈ U' := by
      intro k hk x hx
      obtain ⟨hxV, hxU⟩ := (hmem x).mp hx
      refine (hmem _).mpr ⟨hs.conj_mem_N ⟨k, hk⟩ ⟨x, hxV⟩, ?_⟩
      have h1 := hU (Ψ ⟨k, hk⟩) (Subgroup.mem_top _) _ hxU
      rw [secModule_act_proj hs Ψ hΨs hΨk.le] at h1
      exact h1
    have hnorm : X ≤ Subgroup.normalizer (U' : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun h => hinv k hk x h, fun h => ?_⟩
      have h1 := hinv k⁻¹ (X.inv_mem hk) _ h
      have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
      rwa [e] at h1
    have hcle : V ⊓ Subgroup.centralizer (T : Set G) ≤ U' := by
      rintro x ⟨hxV, hxc⟩
      refine (hmem x).mpr ⟨hxV, hfixU ?_⟩
      intro b hb
      rw [← hPS] at hb
      obtain ⟨t, ht, rfl⟩ := hb
      have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
      rw [secModule_act_proj hs Ψ hΨs hΨk.le]
      congr 1
      apply Subtype.ext
      show (t : G) * x * (t : G)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_iff.mp hxc (t : G) htT
    have hU'eq : U' = V := hgen U' hU'V hnorm hcle
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hs.proj_surjective w
    have hv : (v : G) ∈ U' := by rw [hU'eq]; exact v.2
    exact ((hmem _).mp hv).2
  have haX : a ∈ X := sup_le (oTwoRes_le X) (Subgroup.map_subtype_le _) ha
  have hσA : Ψ ⟨a, haX⟩ ∈ alternatingGroup (Fin 5) :=
    (mem_oTwoRes_sup_iff hΨs hΨk haX).mp (by rw [hCc]; exact ha)
  have hker : ∀ y : ↥X, (y : G) ∈ pCoreOf 2 X → Ψ y = 1 := fun y hy =>
    hΨk.ge (Subgroup.mem_subgroupOf.mpr (by rw [hCc]; exact hy))
  have ha1 : Ψ ⟨a, haX⟩ ≠ 1 := by
    intro h
    apply haN
    have : (⟨a, haX⟩ : ↥X) ∈ Ψ.ker := h
    rw [hΨk, Subgroup.mem_subgroupOf, hCc] at this
    exact this
  have ha23' : Ψ ⟨a, haX⟩ ^ 2 = 1 ∨ Ψ ⟨a, haX⟩ ^ 3 = 1 := by
    rcases ha23 with h | h
    · left
      rw [← map_pow]
      exact hker _ h
    · right
      rw [← map_pow]
      exact hker _ h
  have hidx' : idx M (Ψ ⟨a, haX⟩) ≤ 8 := by
    rw [← hsd.secIdx_eq_idx bot_le haX]
    unfold secIdx
    rw [fixSecIn_zpowers_bot]
    exact hidx
  obtain ⟨-, hiso⟩ := irr M hnt hfix hgen' hσA ha1 ha23' hidx'
  rcases hiso with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl (isModelSec_of_iso hs Ψ hΨs hΨk e'.symm)
  · exact Or.inr (isModelSec_of_iso hs Ψ hΨs hΨk e'.symm)

theorem irrSec : CFSG.Quasithin.F53.Stellmacher.IrrSec := by
  intro G _ _ X V T he hVX hXN hV hC hVc hT hgen a ha haN ha23 hidx
  obtain ⟨e⟩ := he
  have hs : IsSec X ⊥ V := isSec_bot hXN hV
  have := hs.normal_subgroupOf
  have hCc : cSecIn X ⊥ V = pCoreOf 2 X := by rw [cSecIn_bot]; exact hC
  have hsub : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X := by
    unfold pCoreOf
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  set θ0 : ↥X →* Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)) with hθ0
  have hθ0s : Function.Surjective θ0 :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk0 : θ0.ker = (cSecIn X ⊥ V).subgroupOf X := by
    rw [hCc, hsub]
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ x ∈ CFSG.Open.pCore 2 ↥X
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨Ψ, -, hΨs, hΨk, -, hPS, -⟩ :=
    (secData_secModule hs θ0 hθ0s hk0.le).exists_normalized hθ0s hk0 hT
  exact irrSec_aux hs hCc hVc hgen Ψ hΨs hΨk hPS ha haN ha23 hidx

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
