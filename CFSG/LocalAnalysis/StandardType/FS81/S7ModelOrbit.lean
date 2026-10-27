module

public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

section M6cData

private def tabChunks : List Nat :=
[
  0x82637208c191c904951c18814aa6080f0d663a954c1a840a8e09418d3636c71c098223a6004081c63a071000,
  0xd5304e0d8f1528a334d4198423ae0da9c847a120d68cd1908b4a422d29a73460cc1a9a506a0dc518a535240b,
  0x8739f742a658650e33ae7d8eb9b73ac7d8470ac72900d443eb45c22d263e3550f2835a6f51a9c83708e116a1,
  0x859a361668dd2ba14628cdd1a3346aa8551ba760a41c1ab072120ddcfb0c742e758579f61525d8610cf42e8d,
  0xd1b2545ac8dd1b0cf4aa758851233e8bd18a9b61d4404faa174ae75cfb2153aa7dd3b0914ac2ccfb09342e85,
  0x4f09cb51684873a333e433d090c932438857a334a431d09a313643a8819f34247dce99f242c2b8663b342c39,
  0x8483e545a83d25092160f3227a4885c424e31221d26b88046a4ac8d873a2f49c33d23a6741e8b90aa013d69a,
  0xcec95a2244cccd9ba31e5eccd1ae1a43c1cc4234d102d070b345900d443ea12693d36a4a1242c859a6750c1c,
  0xcdc8b91b2468a31652744b8a71622923ecad97a3164ecad16b37444ced99a1e66e87893a22444ced9fa2666e,
  0xcdc93a21a468979991b23e8a79db3f65e47c91b2f6668b516a30256cad97a296768979f91f66648c91b2f24e,
  0x1ad9da1ee7ecdd0d73b4354ad0f61ee7ed0d1173b67e4bd0f622e6eced1b33366e8e90b61a8de8928fa28a46,
  0xcdd9da3e26e4eda5a16a8e86b9da16e7ecfd0d743435d0da3b3f0be18da18630ce4fca1b4b41d84a33a12c2d,
  0x4dc99a3446249d1c2352564bc99b5367e88ba1a460ae909a1a1ee8e4dd1362ae7616c2f93344589a9d93f68e,
  0x47c93a2cc614ad14e2dc608b491b2f6668d595b2f4628e025a3547813d1c92b66e4bc97a2dc634ad18634eb6,
  0xd1d1134b2668a9173370ae16c97a264544dc9db4b666cdd1cd3326ed3d9fa29e8648d9b92724eccc95b3b236,
  0x8999f736c44ceb1112ac4c8799f742c44ceb9f52ec4c8a99b73ac6bccb9b639c3c8883b74344cd1d20c5347b,
  0x4bb97732c5acfb14f42a45cda93526e654ab9d51aa3d49b16630a558a716e3045a48b97732c6acab97631675,
  0x8d51c138c628d09ad3025ad5714522c5949b9d52ac4b49b14f36a3d48b12f3ee85cca91526e65cdb18a29458,
  0xd17a4e22691d339cf3dc734e09ab4d2684c5a8a30a538d316d2cc634d1af9311338f11c89cc708d59cd29a5b,
  0x8b79d12224c8a7a134666c498953366748d516a30264cc99b231124d044722a2618b91312dc5425920e3dc4c,
  0xce90f73e43d4b91161ae84d190f73e6844c911626e74cf91d3366748f90d61e8f48b293230a54cf897229a54,
  0x86a3ec8de8a22713534c5588a98e2692291921222e83d170f744e91cf7a0e3e2784e5a493826ad359f222e84,
  0x8eb93f2bc7d88b13473910d2442b3dc35d064234d10285ba2f49a8a85b0d61ae91d33096169015069ef4542d,
  0x47917632c6d8ca8b323e4f8eb8ff23c6dcbf15733e5789b97e26a3b8ab15733e6f8bb97f33a438ab1772be5f,
  0x4468ae32e67cdf93d14a31c9f95e36c6d8ea90b23e4f8cb99e2ee6f45995d1a234c9e8f32fa1c4488d232c6d,
  0x44189e5262fcbe8290865742486249e3fc6e8210064f4228272be2fc6f1ee2ea2a8ca8cf2fa3b8aa8ca2ee57,
  0xcdf1933ba23c9e8ad14e4746399d09a1b4551b23a2328c91b23a46c4458ff23c7cc6f8fe3a212cbe8610d657,
  0x42997f1be3f8e686f2ba23cdf1eb33a21c9e8a64164fc8e88a39c7b91591f1fc7b8e68a90da13cbf2063ca32,
  0x46286d09e5f8f720d194819128e90e6674488932fa2cc5f26f1be5742887327a1c44927323e3f4288332ba1c,
  0x8d99bf3be474428a723e4f8e91d23e23ac7f91e3646b4351cf1fc8ac8f8de4963f8e59bf33e474468af1fa29,
  0x48b13a2766fcef15b33e6f49b13a2b65fccf1bb2be5f8ed0fa230df8c888a3622bcce8ce2e22a8c993d0da23,
  0xcee8d72fa3d47b95d22e6744a8b51ec5e8cc9162b45e8cd1791ae4fcaf1bb23e4f8cd99e2766fcbf11b33c46,
  0x86d0f86bc5646b1791ee6748b1391ec56cbe8b51ac5ecdf9df2ba3547b95f2fc668cd1b926e4fcaf17b37c56,
  0x4f7a3e1342e18f0ba1b0cfcdf11b3be6787d9be1f24c88d11b3be7f89d9bf3ba5488d13b33e6f8ed97f33c7e,
  0x16e96e274564d49c343e67cdf21931268d1f0d94143ecdf0db3be7787d9fe1f67fd0f9dc5b8bfcfe2fc63a73,
  0x4a319a3724b8dd1db57a604b51da372438fd1d924a524b1a7f3bc4ecff25853c8ecff11b43a618ad17b378af,
  0xcce9112265f4999bd1623448919a3724c8bd19a3746647995f2fc76c9f95e3747e11f1da430978fc92f33a53,
  0xd5f9fe2b68791c27e4368789da3d2cc5e8cd99c538af4a715a2f2624d1a3f2fe678fc96930697cef17b3fa3c,
  0x92722d28c9992292e4607f90925043c8c47799d21a418e91f11dc7c909a7d2824a9091f121c8c90892521248,
  0xcaf93e45c834788b11266f923225224930ef22f43c92cffa3e4d68793599f2fe8f4c096b4ba584a419c37e67,
  0x43b97d0ea2593791f1fa1541b95d0ea15cbf8df1fc8345999d1a67f9159dd1a65f47924b2fe5746920e45c9a,
  0x46b93d1ee6f43a8951ac748f88f6364748f91d116e47c9f2131fe478f887733a2544b97d16e2f95b8df33a15,
  0xcbe8b73bc82cde8b72ba3591595f27a2d8f720e4964fc8f20e3da3544a87733c899028f73bc6ccfe8b72ba35,
  0x8fb91f27c7590a21e3ec8d11f21521e5f49692636c754871d63eea74b094a3ec754772163ea4149494353a25,
  0x4b49834be57cbf21529258d3f9fe32e8746997d1e23ccae9133ba244588f236c7548919636c758da8d327e57,
  0xccd9b92745d8cb97b3347dcad97a42c4d8aa3bb43c5dd1f2544bc8dd1f1574ba518cb1b72f89f14e92e2ec65,
  0x48d9991322e47d1b63aa468cb1b63ac6d46d93b2b47dc8d93a3ae668bb9bb2f455ccd1552345d89b9bb3b455,
  0x47d9992345d47d1972f22e46d17737676cac8d91f656cbd1d632c6d49d93b2b46dcdd1973b236cbc8f91f656,
  0xc8d1f10f66644c89b2f22ec5d2731b66642c87b2f21e44d26f2363e42c83b2b21e42d97b1b63e9071951b46d,
  0x46c8990f6669132051f6768d99f91765646c8db2723ecdc879132368e91f11f46c8e91f23a22ec8d93a4263e,
  0x94993b2321e42d9791321eccd8fb2347b44d979176769059b91765646d22b2b64e45d1ee41c92c9d91a41c7b,
  0xced9bb2722e46d9191b23e44c87b334738f68fa3cc8148c89b3722e45d9991b6369278fb2f21e44d9591322e,
  0x47d1911b46ccac89917464ced9fb2722e46d93b2b47c8d91d123646c9d1d239a268f791a4164ec7d22b2347a,
  0x8f88ee424744831f1306a34b45324a48c2a92324265b49694e4248c4b31f2422534b094b5a46c45d1d11b66e,
  0x2d19aa48c994b720d1a48bca924b2e64c93595245684cf99711e244ca8911262344599d241c8b49922648a54,
  0x4971f642a618eb1f52da50495aad386924d596e4d6634d1a6931492d17a0cadc9391726b48e8991724d30962,
  0x8bba2f49c55d23a6731e6b90a9812d69a4b094b514754871f636a498ea9635625228b2364294d90b1f731a43,
  0x4891b7322344791974268ccb88f12265ccc91f636c754a99532e47526b9c896c654a31b62ea4b8ca4f64ac8d,
  0x46a8d736a3dc7b26f22e6544a8b72ea2d46b2b72ae4d44a87732a2d44b9b722e4d9071b51e4754899f126465,
  0xc9b9563e47b45b20f26c8acab9164964d9059f73ae5546a8f726a3d48a8b512e6d8f720d22c8191293516e75,
  0xcdb1db2ee658fd11a270f58e88d63e23dcea9163623d8e997516a358d99f742e5546a8f72ae5d9091d23e24d,
  0x8dc9362f4668dd1991ee55cbb1db26e558dd9b62b675ccb13b36c4e49b15a23675cfb13b36e754ab15a2f665,
  0xcca8d51ec56ceb9f72ea3d48b97732c6e8bd1992ae55cbb19b3ac5ecfa8f732a4548b97526e6d45a8d522c66,
  0x4a31b9306b54b44ee4347e2831fa3b66b49694e3b47e4d31ba3b2634b094b51c5e47b19922e6d49b15922c5e,
  0x8dc4b33d1248bc966334564a71789a48e90d15b41e8b89da2748e6bce71f934262d249812d69a8dc92e3b466,
  0xcc99b24343e88c3f2332448dc9333a2548bc9323366c4789122f67cd099912224ccc99b23b4668dc9732e664,
  0xd03a2739e7b90c9c13568a4d098b4967489d9f336446ce91192a44e87d9f342446ce99f12e44e8ad9b33a47e,
  0xd16a0a1b43e87da2748c2e86c4253da73d050da1f103247a088dc564c317a2725b8ac4aa4b48e89d9ef41c46,
  0x8bc93a33466ca59623764aca095a3346ec839264363bc8723a2b45e1cc46345112ce70fb3d910d2442a1b683,
  0x8dd96d1f64448c91b1e24ec968b91b2468ed1f92746e8ed1fa3b23ec698f24362cc691fb25466ca190a2f648,
  0xc8b87712c8e8dc8fa3b246c9693a332468dd9091b23e8ed94b2c63a47c91b1ce418fd1fa43256c678ee3b653,
  0x90d1f91b62dc6b23b12e2d90c89b26a2e45d9151b61596d8772621e44d9111322e94d8b712a1e42d8f51321e,
  0x90d23a4f635c5b23a4323e45c89b26c9691c91b2e476cc88db1ea3e47d8d52365444c8b91f47e90c91a3b47e,
  0xc4990d1322ec768b91b4aec698b11321ec888b91364cc498b24322ec8a8db2ec8ecaa8db1ea3e92d8f71aa36,
  0xc5327b18e2394d8ae43658ca58c91b23ec548f92322e44d92e4749648d25a4f24e45d9511b236c988fb0e4ae,
  0xc212723b2368fc8fb29a468dc8fa3b63a45c8da3f65acc18c91b23ec638e64348691c93b15e338fd1f917486,
  0x9e48ed19e2a4828e711234c988f11e64448980262608c9a8b11a6454688f25a618c248b11262b4688b319e0a,
  0x48534a6c23345788b2ae5d9c48e518e1a47795121cca4753426124299090a71ceb9838a710cbbc4786f3265c,
  0x44a8b726a2d46b2b71261c44a8771a22d44b8f30a61c92b84668e199a690a6de0b99784d1d4da9c19351da43,
  0x48a9171524dcba8b51aa4590b23526c7d90b23642a3dc438a64ae1bc4723516e4346a8d71da3dc192f70a655,
  0x46b8e91ee5092b9291ee3248b27718e2947b2364aca5c5788e4ac8d48a8d516e4393b25526e658fb9b51ee32,
  0x4778d124a41c5992254e42c8128f1d4b24a72e255e41c732c71de3301f2aa58650c9540f24642a132ae51a5b,
  0xc572724a24c4788d31dca493895121e4b497309214c897492a6024a9d93d25ce34c592cf16624cb794e7e243,
  0xc788f1224bcc4b8751a22cc6a8f11a63dc2b8764a23cc849132449cc849131d24c9498e718a4492927256633,
  0x495341254db9c73271ae2d9878b712e6dccb3a921a3bc6a92520e2d47995522244c9a93306cbcc2b9111a23c,
  0xc4b36d254e3c2b30f0ea429a53632224349692a654d04768cf16e4cca93a920a39c4a90f2ea4b9a490a6c4ca,
  0x9492b12e62b9738cf18cb3c732c8e7cb89379031d4a1c919092dcba9818cb1c501c759027dcab96698f0ecc9,
  0x4778d321e4b9e892520e2c9188f24a6299598c711cb4c5725324642c649112662a4989511e234c7727252254,
  0x47b2d71662445a8971e23545b9130e62491b89260e2c9c894a7661c977891254ca9a18ed25a534a530a64243,
  0x91b9432562a47a9171124549a8d516e4392b27526c9d94a9551ae5c47a8f72a245c292d70e63b45a8d719a35,
  0xcb69363aa458fb8c91aa3d90b98b3462a47a91714e3191b2364aa55c478ae42c8546b23710ca5c5386e56e23,
  0x8ef95a2fe5ec9d15f2b45748f17e2fe5eccd19f2b65e49f17e33e4ecad1ff2364e90f13e2b8dd8fa8f642a45,
  0x8ef1fd27e3ec8d1bf2f467ccc8df2723f47f91923e5644e8bd1fc6f8ee91e33c6f8ef1bd1be3ec8d1ff1b63e,
  0xc6d8b90ba0fc8c87d0be4ec4d8ba43c6746f1bd1fe5648f17d1fc67c9c8bd1bc6fcbd99b2323747f91b27477,
  0x44e8de3bc7f47f1be3bc7f8ee8bf1b63e90f8bb1b47f43f95913a27c9c8bf0f4afc4d9590ba1fc9c87d13c9f,
  0x45f9191bc8fc8d8f917c7f90f25f1f63690f1fd1ba2743f95a47c8747f99a37e6e45f9191ba37c7c8ff2f21f,
  0xcbc8bd17e5646f89a53e2ec9c87d13e4644e8be53e3ec6c87d0be4e44e87f2b62ec6d1fd13e4e45f99a43e5e,
  0x48f8db1f4778ee89e3fe3692f8fb1749fc6d1ff3365ec7c8bd1be3646e8fd13a1fcad21e47a3f91f25d23a27,
  0xcab9763be4dcab1fe23c4f1a91bd17c7746f9791fc6746f1bf2322745f1df3366ec7c8bd1be3ec8d1fe3fc87,
  0x8cf1bd27c5f8cf1be33a3fc8b9363be3dc8b1bf2ec57ccb95627e5d89e93e2bc57ccb9b62fe5dcca95e2bc5f,
  0x8bf9551ba3f8cf99736e4d47e91f26e558df1be3ba57c8b93633e658bf9b51fe5548e91f26a4fcba8bd1ba47,
  0xcb911f324474af13e27e6cce915f3266c4bf13e2be5ccc91ff2a65c90f0fe238cb8be8fe33a47cba93e2ba47,
  0x4efa0a1fa8f88f98e1fe6bcd311f38c47ce79ef350ab1679c8588b94fea1f4142f86e2ea1bc3f18599227e6c,
  0x49f21e3fa574be99f49e6b8af9ce4f89c92f9c627e794df17e33e621482b133c578be9dd3fe7acb798e47a6f,
  0x4af19e37c778de91f266548ff9132647790e2163fc8f11b21d2be5b4be97e37c774af1de3fea54de99e3fc77,
  0x8cf1bf2d09d14a97e2fc674de9df41653cb721d33a6fd159b233e7448f97127a4fca895f3223747e93e37c77,
  0x92e91f2da4f49f1fe43a4790f23f49a5f4af23e43a4f92f23d2ba4f4afa9339c5fcf725c4ac8fcf315f40a67,
  0x93e1ba4be7b93f9cf40ca7cf329f2de53d049bd33e8a4ce97c2f066cb527e4ba5f94f27d2bc970ed23e4f87e,
  0x43f95716e3591e8df2e23fce925f3623fca891e4fe54c988fe47c9794f9332249791e91d1ba2fcc927e4ba4f,
  0x8ff21e3fa37c7b91647e35c7b21d13e5d45e8bf2aa37c4b2df16e5d43e89f2aa2745f29f1ee3543e85f26a27,
  0x46f21e47c9fc8b8f647c8747e8bd13e5d92f23d23e6d8ef9d51be4d47e8ff22a47cca89d17a3f8ff21d23c77,
  0xca695d2bc778fe93e3fc87d3899d2fc878fe91e47c8749e95d2fe9b45f9551be6d91f9951be4d47f25f26e45,
  0xcf88ff2a24748f93127e6c45e8dd23c778fe93e37c778ff1dd1fe44c9921f1e6448ff23c3f48792e21a47a4f,
  0x4ba9975ae7b8cfa0e4f88e92fa062fe894bf1be3be5212c2792bc678de99d37e8ac9794e47a5f4cfa4b3a46f,
  0xa996a56ca54db2d656a6594a18e4ecad0d32952ae5b4ba97646c954ab2564ee834da9964ec954bb2964ea65,
  0x94b2d72664494b2752aa4547b95256ca54bb2b42e4a5cd72b731e7196b9a65ae5bca79c93ea75cf49d53684c,
  0x9879732a4c9ca9930124c29919b33251ccc9972924c39769cd22e5c49b99252e5c49b9512acadca993126c9d,
  0x96996f34cbccc32f331e5bcd4a113e6724f89d02184bcc52d2562749792d1366649839732e4bbca9329364d0,
  0x4d79ae64e63a70a4a996719879a418cd29b19c945a8305732a6803a0819ab35e63a560c81c67296814a56663,
  0x4a692f22a594a38f72ecb9cab95659e4d98498e644bbcab93660e4dc8a0765d4c0ccb9768ae5dcab4765dcb3,
  0xc8b8f6564a44b89312264d9692b132253cba96e692529b13292d4d04b53f682cc9c8b8f661e3dc6b9b732d0d,
  0x4799391e24497989b0f2344598d91e234c7d85b0f4a44999552a65d9599552a64d4b92d326e454a9292564bc,
  0x99492a6824a9d73ce64e36c5d30f17626cdd99a7d2434778d924a41c5c8f32b2444899392660e99985b2b234,
  0x9b389a6da4a9c785a69e1e48538a7465648692d254da9c08ed19e2ecbd99a7524147389921e5e497349214d8,
  0x93b89b1749546b9391ea3dc8c9170b4c5c3d97916a35cac8d51ecb5c5d89916a25c7c8d516e46c3d89a4ee1e,
  0x93b25526a3d46b93a52c9d4ab9ba42e7648b8f926a4dc6c9573323547a93646c954ab21646c9591a91717636,
  0xc8d8f80b4b297197b2b50bcad93a88cb395698d1ee4648b97a4ee5648b8f926ca5c7d8d922c9593b2b71b62e,
  0x99094a7a4fc9838fb1b4bbc6d8bb3365ea0892d21e3e4a29271b65696393b274abc8d2e92dcc096793b234b9,
  0xcad2932724cc8c95256646c7c9324e4a49698fb1b4a49389512223cc8d2b25225c49795929cca49534261252,
  0x94c97a4f06d92d2983ac9e49d94d2b25690d2392748e92da2d3325e92d2392b49e92c9792b25ed589132724c,
  0x49c8f91b65c94d2792b4a60cb27b39ca6cd79e65767195d94f25e7a4ec9bb4126e4cc1542ee5294d279334ae,
  0x95d8d716a2643d91517226c9b89716c9647d9512366c93d9912364c49d29b2664448d25a4f4aec898f24f496,
  0x45c8d92348691c93a3f48691d2191f635c7b25b16e3591c8bb2aa3646d9351f61d97d89732a2645d97517236,
  0xcba8fb22a4693d9171ea3e91d25a5363dc6b25a4724646c8bb2ac9e92c93b3ac7ecfa8fb22a4648d8f52766d,
  0x92c1d24749e0f92592b64b4bc97a3f4864ad21a476944dc99a4748649d25a472564bc99b51a36c9a8fb32c96,
  0xc972593326ed359f23b68448d9312724ec8895b3a23647c93a3f4864ad1da3f4868fc91b1e64491d8d31e486,
  0x8ed93f2bc8ec8f93e4b45e8cc3bf41c6ed1729841c9ed1319b48a668ed1fb2508a12097a374764dc9db49643,
  0x49d1fa432568ed1fa4347e48d8ff23c8ec6f8fe436578dd97f27c66caf1992b46e8bd97f33c66caf97d2f46e,
  0x49d1db27a3e48d1bb2fe67c8e91927647c9f21a3b47e4bd8ff23c7ecbf1db33a46c9e939276474ad95d1b23e,
  0x46c8db27a3ec3f2bb13e5744c8bb27a2e46d2bb1be2f44c87b23a2e44d93f13e2f92d1d92347e49d95d2b46e,
  0x93d259276678fd9bd1f64748c91b1fa4ecbe8b91b24690d2392747e90d23a4323ec6f8fe4b62fc6f23917657,
  0x44d93d1b22ecaf8bf1bc8e46d93d1f66792d97d1f64748d27b23e3f47d23a4b4a6c7f8de4b48e48c8d917657,
  0x48d8dd2324e46c8bb2bc8691c93a474964ac8db2fa3e47d95d2362794d8bf27a2e46d91d1b23e96d8ff1ba2e,
  0xc8e8d91f476ccf9bf1fa3e48d8ff23c8e8fd2192b637c7f21a4323691d8de4b63fc5f27b1bc8eccf97f1fa3e,
  0xc9e93307cbcc2f95d1a23cc9e8f1224bcc4f87d1a22cc6e8f11a63fc2f87e5247e47d2192365f49d1d92347e,
  0xc4e90f2fa4b9a490a6c4ca495341254db9c73271be2f9878bf13e6fccf3a921a3bc6e92520e2f47995d22244,
  0x46a8b723e1fc4f2770fcc9c4f36d254e3c2f30f0fa429a53632ba4349692a654d04768cf17e5fccf3a920a39,
  0x90b2364ac8d48b8bf1bc9dc4f8be4aa35c9e8f51ee4748b85e5ae1fcbe8b51ae5746a8f65ae2fc4e8b512e3f,
  0xc6e9164ac9d95b8df17c9d92a9351ea35c9f2964ea55cdf2173ba45c7e93526e374ab99d1aa3d49b2364aa55,
  0x97496e604b3c9f91e5ce47c7e002594b8cbf95e7de57c9f40659cab4c68f723a45cbf2772ba45c7e93652e3f,
  0xcae94e6524a9a1309294c84a5392764c1c7f8de5de37c5f99f2fcf449690f1fa514938df2bcb1c9f93e55e47,
  0xc8f87f13c9c48993d2665794993d266474a92b323e3f499272524b4c7f8de5249c4a89111e6479592912e24b,
  0xcef9be7124b4878fd28a49c6e9132fa4c49995d2a61796987f27a3c48991d2224c9898bf13a3c4698fd2223c,
  0x49694d294c299090d1de37caf97e792494838bd25e674a7369254e09a494a6c2529a736e68e3fc6f32f1be2f,
  0x96128f27e4795395f27a639652e31fe47a1391f27d039472ad35e279838be71a529d787e5de2749532a6864f,
  0xc6f2931fe2f9598de4e657c9f8fd26254c6e9512e24447991e4a49c4b927252264c6f2c71fe3f95791e551c6,
  0xc5f25717cb9c6f3b12d4f4c4f2cf17a5298532323a534b696a5d4c049690f1fe4fcaf3f128a49c6f2512249c,
  0xc9f2364aa5592b2752ea3dcce91522e5f49b87e56e27c8e8d51ee3f47a9165ee37c5e8d516e4747a8d727e27,
  0xc6e91526e37c7f25642c8d4bb8bf1bc8d91a8f64ae2f93b8df13ca5c5f2572fe57c6e91526e2f49a9551ea35,
  0x95b294b6ca593b94d32a6d93b2953ac9593a9b53aa6dd7b21522c8d49b99d2ac7d49b2171fa3d48b1f737e77,
  0xca99125ae4c94b9b3326544aa9772625d4ca93522e5c93b29532ca595a9b64aa5593b2352ec954fba2d3a965,
  0x51b9e942e5396b96d42e824fb2b739e6b2eb2b652cb5cf39c652cad4fa5f4c2e6295b2d53ac9d49b297264ad,
  0x9589b2564b44e991660e4dc9b2ef2acba36930259e5dcab2e732e5d4e730a6464dcab4772ae5da2b2ce5da7b,
  0x9a096d29e4dcbb99686a614b3916522549599165a64dc7b2f322cacccb97726a5c4c99153226c4a89332aca4,
  0x9839b33227c9953432a65ca499733251c97730d41e3d9939167ea6aa0b8d661e3d4c534a6c6554c69ad354ca,
  0x34534151538a6532739e6b9879e738e5bcc74acc5993ce4644cce7ac993272a654987972611ab9912ef3265c,
  0x51996e5e6635199e9424b4cd798cbe4b49592f338e699592d1421843199aa5a4bc4f8a6f352939a466a6c4ca,
  0x93d2993348e49d25a4325691c9db49a6e2bd29a4f16693d25b25a5e4cd25a4f26e91d2593326e4cdad14a672,
  0x94c9d8bb17ecb529a5726e92c91a4f64494d9331e4aec8927b3a66cc989392b6444ac9792323ecc925a4f25e,
  0x91d94d2b25e91d2593b48691c9b93325ed56a1b4127ec972bb29a7ed149da5367bce65ba5349e95da073cc9e,
  0x29d29a4f46ed17a4e33691d3394f2dc964ec9bb4d26e4cda8a4325691d1f92f4864dda713315693d258af496,
  0xcf897a3b2568fd9512324e8eda134664c49c95b2665491d1fa43266c8993243146cc44fa3b2668fd1b92f476,
  0x4bc8fb3aa4648d9b52762d95d8d72aa3647d9351f24697d9171ea3645d9551f236cbb8d71ec968fc93a43256,
  0x90d2392f63dc8b23a4723e92d8f64f645c6b29b1ec96cdb99722a4649d8f52725647c8db2ec8e92c95a4b49e,
  0xc6d8b92223cc8c9312264ec4d8ba5248648d239276754ad1f927486c9a8f92347ecfba1722a4649d91726c96,
  0x9c73672363e9a78fb1b67eced3a929a4bc8c96528e3e4999992a254cbc9730f4bcc4d9592224cc9c9312a4cc,
  0xc4d30f172529a53632b2534b696a654d049690f1f65eccd3e928a49c6c94f3725b9c494a744da4b53812d4db,
  0x97391b234b3c9d2c8decb895795b274b1cbd95935cba98191b27511c9d95a85cab9669cf174c9c6d3ad2d4f3,
  0xa0896528e3e9389325263e95991b1b4b4c7d2932f656c8c9512e63e4b899126244c9d272522649492b13663e,
  0x47a8d72724547b95b1763693b8da60e3e9e898a7e62e9778d92d4ca9a19392da634c530a6425349791b2b65e,
  0x49a9571b2554ba9151ee5692b2752ec9d94a99522e6e49a93733255c4d2d71764e47a9172324549b3171f636,
  0x91b91922a4d90b9db3f63e49a9571f64693b2364aa65c6d8fa4ac9548b2771b4a5c7d8ba56e3693b99b2f63e,
  0xcad17f2f45f49f19e2be66cdd17f2f6664af19e37e56cbd21f2765691f15e2f8f691a9364aa55cdc97642a55,
  0xc9d1df3346fcdc8ff2b24748f93927e5e45e8dd23c778fe93e37c778ff1dd1fe46c9d21f1f6468ff97a33e66,
  0xc9c89d0fe56c5d8da47c6f47f1dd23e5e49f19d23c6fcac8dd1fc67ccd9bb2723f48f93b2b47f8df1dd2be46,
  0x48f1de3fc878fe8df1f64691f8db1f48744f97917a2fcac8df134a7c5d9790fa27cac89d17ca7c7d8d90fa17,
  0xc9d9191bc8791f27f2363e91f21d1fa2f44f97a4bc8f48f9ba3be7646f9391fa3fc8c91f3322745e8fe3fc87,
  0x47f8ba4fe36cac89d17e4e45e8de57e46c7c89d0fe5645e89f2f636c7d21d17e5646f9ba47e6646f9391fc97,
  0x8fe8be43e3e91f91b1b497c7d21f37666c8c8dd1fe3e47e91d17a27cbd1fe43a4790f23d27a2fccc8dd1be5e,
  0x91e97d33a5fd591dd1bc7f47f99923c6f47f1df2722f46f1bf37676c8c8dd1fe46c9d21e3bc7f49f8fb2347f,
  0x4ae8fd1be6c91f25d2bc9793e97e43a4791f1fd27c874dfa6d3395493f25cae49791f94d2ba5f91f25d33c87,
  0x2c727e4bca7d13a064bc9f4de5a8b866293f29d33c8f47f25f2649fca991253e4c92f9f33a65448e93f2624f,
  0xd4897ca6c9791e55647c87cb693d2bc8791e9be3fc874ce97d2bea34ffa293be5394f96d3be924df27f41e7b,
  0x26b1bd2fc778ce95e3794593f25e33e83d1717f44e91cb798e47a6f4cfa4933a5fd351fd27c878ee95e3fa67,
  0xc7b91647c7748f1fd27e744af1bd27c77cb88fd23c6fcf9a132a24749f9532e4878ef1fd2fe4cca91fc9ee6a,
  0x45f99643c8f49f23e4ba5746f9b51fa3fcca91f1aca7c7b97517a37caa8dd1fcb7c9b91517a27cba8dd17e65,
  0xcfb9351fa47c9b95647c7f90e95f22e4d90f21d1bc8fc8b25f26e3d93f91647e75cdb9351fa47c8a91d27a37,
  0x89f9b73ac57ccb9b52fc5f8cf97732c7fcab97643c4f8ae3f63fa3f90e91f36a4f8ee91e3fe5546e8fe3be75,
  0xcba93d27e554af9951ba3f49f1be3ba578cf1be3bc6f48f9372ac7fc8b9363be658bf9b72ec57ccb15d2bc5f,
  0xd3719d23c6f49f9952bc5f49f19f2ea3f48f17f36e75caa91d27e55cbb1de33c6f4bf9372ac6fcdb19f3aa47,
  0x4ee9bf4526f4cfa4a3ba578ff1bd2fc774dfab53394391f21ca4c878ff98d2ba5f8ff21d3bc778fe9bd33a5f,
  0x49e95f2e6648ff1be3ba67ca99723b934ce44b233a678df17d2fc6727925e47c5fcf7a0e2be81d1398f35c87,
  0xcf913f366744cf15e2fe64cd921f2e66491f11e279048de93e3ba57cd897e33a578df99123a4f8cf9d33e65c,
  0x8ae99e2f93293f25e2be73cf713f3ce81cd79ce47a7f4efa093ba6fd159b22be74cc913f3644f4bf15e23e74,
  0xd0446b35c47ce64634511287f9ef41a8f87f11e23e81d130de1f91150e9ff3d43f88e42c95e7a24717d37c67,
  0x120,
]

private def tabEntry (u : Nat) : Nat := (tabChunks.getD (u / 32) 0 >>> (11 * (u % 32))) % 2048

private def letter (u : Nat) : Nat := tabEntry u % 8

private def letterFin (u : Nat) : Fin Tag.E8.rank :=
  ⟨letter u, Nat.mod_lt _ (by norm_num)⟩

private def depth (u : Nat) : Nat := tabEntry u / 8 % 64

private def cls (u : Nat) : Nat := tabEntry u / 512

private def dec (u : Nat) : Fin Tag.E8.rank → ZMod 3 := fun i => ((u / 3^(i:Nat)) % 3 : Nat)

private def enc (a : Fin Tag.E8.rank → ZMod 3) : Nat :=
  ∑ i : Fin Tag.E8.rank, (a i).val * 3^(i:Nat)

private def repCode (c : Nat) : Nat :=
  if c = 0 then 4790 else if c = 1 then 817 else if c = 2 then 5 else 2450

private def parent (u : Nat) : Nat := enc (TableBExc.torusRefl .E8 3 (letterFin u) (dec u))

private def mkVec (c d : ZMod 3) (rest : Fin 6 → ZMod 3) : Fin Tag.E8.rank → ZMod 3 :=
  fun i => if (i : Nat) = 0 then c else if (i : Nat) = 1 then d else
    rest (Fin.ofNat 6 ((i : Nat) - 2))

private def tail2 (a : Fin Tag.E8.rank → ZMod 3) : Fin 6 → ZMod 3 :=
  fun j => a (Fin.ofNat Tag.E8.rank ((j : Nat) + 2))

private theorem vec_eq_mkVec (a : Fin Tag.E8.rank → ZMod 3) :
    mkVec (a 0) (a 1) (tail2 a) = a := by
  funext i
  fin_cases i <;> simp only [mkVec, tail2, Fin.ofNat]
  all_goals exact congrArg a (Fin.ext rfl)

private theorem chk_decEnc : ∀ c d (rest : Fin 6 → ZMod 3),
    dec (enc (mkVec c d rest)) = mkVec c d rest := by
  decide +kernel

private theorem dec_enc (a : Fin Tag.E8.rank → ZMod 3) : dec (enc a) = a := by
  rw [← vec_eq_mkVec a]
  exact chk_decEnc (a 0) (a 1) (tail2 a)

private theorem enc_lt (a : Fin Tag.E8.rank → ZMod 3) : enc a < 6561 := by
  have h1 : ∀ i : Fin Tag.E8.rank, (a i).val ≤ 2 := fun i => by
    have := (a i).val_lt; omega
  calc enc a = ∑ i : Fin Tag.E8.rank, (a i).val * 3^(i:Nat) := rfl
    _ ≤ ∑ i : Fin Tag.E8.rank, 2 * 3^(i:Nat) :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (h1 i)
    _ = 6560 := by decide +kernel
    _ < 6561 := by norm_num

private theorem dec_zero : dec 0 = 0 := by
  funext i; simp [dec]

private theorem cls_lt_four (u : Nat) : cls u < 4 := by
  have h : tabEntry u < 2048 := Nat.mod_lt _ (by norm_num)
  rw [cls]
  exact Nat.div_lt_of_lt_mul (by nlinarith)

private def GoodU (u : Nat) : Prop :=
  (depth u = 0 → u = 0 ∨ u = repCode (cls u)) ∧
  (depth u ≠ 0 → depth (parent u) < depth u ∧ cls (parent u) = cls u ∧
    parent u < 6561 ∧ parent u ≠ 0) ∧
  enc (dec u) = u

open scoped CFSG.Decide.Bounded in
private theorem chk_goodU : ∀ k ∈ Finset.range 13, ∀ u ∈ Finset.range 512,
    k*512+u < 6561 → GoodU (k*512+u) := by
  unfold GoodU
  decide +kernel

private theorem range_lt_split {P : Nat → Prop}
    (h : ∀ k ∈ Finset.range 13, ∀ u ∈ Finset.range 512,
      k*512+u < 6561 → P (k*512+u)) : ∀ u, u < 6561 → P u := by
  intro u hu
  have hk : u / 512 ∈ Finset.range 13 := by
    rw [Finset.mem_range]
    exact Nat.div_lt_of_lt_mul (by omega)
  have hr : u % 512 ∈ Finset.range 512 := by
    rw [Finset.mem_range]; exact Nat.mod_lt _ (by norm_num)
  have := h (u/512) hk (u%512) hr (by omega)
  rwa [show (u/512)*512 + u%512 = u by rw [mul_comm]; exact Nat.div_add_mod u 512] at this

private theorem goodU_all (u : Nat) (hu : u < 6561) : GoodU u :=
  range_lt_split chk_goodU u hu

private def countCls (c : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => countCls c n (if cls n = c then acc+1 else acc)

private theorem chk_count1 : countCls 1 6561 0 = 1920 := by decide +kernel

private theorem chk_count2 : countCls 2 6561 0 = 2160 := by decide +kernel

private theorem chk_count3 : countCls 3 6561 0 = 2240 := by decide +kernel

private theorem countCls_eq_card (c : Nat) : ∀ n acc,
    countCls c n acc = acc + ((Finset.range n).filter (fun u => cls u = c)).card := by
  intro n
  induction n with
  | zero => intro acc; simp [countCls]
  | succ n ih =>
    intro acc
    rw [countCls, ih, Finset.range_add_one, Finset.filter_insert]
    split
    · rw [Finset.card_insert_of_notMem]
      · omega
      · simp [Finset.mem_filter, Finset.mem_range]
    · omega

private theorem lower_bound (c : Nat) (hc : c = 1 ∨ c = 2 ∨ c = 3) :
    1920 ≤ ((Finset.range 6561).filter (fun u => cls u = c)).card := by
  have heq : countCls c 6561 0 = ((Finset.range 6561).filter (fun u => cls u = c)).card := by
    simpa using countCls_eq_card c 6561 0
  rcases hc with rfl | rfl | rfl
  · rw [← heq, chk_count1]
  · rw [← heq, chk_count2]; omega
  · rw [← heq, chk_count3]; omega

private def wordN : Nat → Nat → List (Fin Tag.E8.rank)
  | 0, _ => []
  | n+1, u => if depth u = 0 then [] else letterFin u :: wordN n (parent u)

private def run : Nat → Nat → Nat
  | 0, u => u
  | n+1, u => if depth u = 0 then u else run n (parent u)

private theorem dec_run : ∀ n u, dec u =
    TableBExc.torusAct .E8 3 ((coxeterSystem .E8).wordProd (wordN n u)) (dec (run n u)) := by
  intro n
  induction n with
  | zero =>
    intro u
    simp [wordN, run, CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
  | succ n ih =>
    intro u
    by_cases h : depth u = 0
    · simp [wordN, run, h, CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
    · have hp : dec u = TableBExc.torusAct .E8 3 (simple .E8 (letterFin u)) (dec (parent u)) := by
        rw [show dec (parent u) = TableBExc.torusRefl .E8 3 (letterFin u) (dec u) from by
              rw [parent, dec_enc],
            TableBExc.torusRefl_eq_torusAct TableBExc.Three.cartan_symm_E8]
        rw [← TableBExc.torusAct_mul, (coxeterSystem .E8).simple_mul_simple_self,
          TableBExc.torusAct_one]
      rw [show wordN (n+1) u = letterFin u :: wordN n (parent u) by simp [wordN, h],
          show run (n+1) u = run n (parent u) by simp [run, h]]
      rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, ← ih (parent u)]
      exact hp

private theorem run_rep : ∀ n u, u < 6561 → u ≠ 0 → depth u ≤ n →
    run n u = repCode (cls u) := by
  intro n
  induction n with
  | zero =>
    intro u hu hne hd
    have h0 : depth u = 0 := Nat.eq_zero_of_le_zero hd
    rcases (goodU_all u hu).1 h0 with h | h
    · exact absurd h hne
    · exact h
  | succ n ih =>
    intro u hu hne hd
    by_cases h : depth u = 0
    · rcases (goodU_all u hu).1 h with h0 | hrep
      · exact absurd h0 hne
      · rw [show run (n+1) u = u by simp [run, h]]; exact hrep
    · obtain ⟨hpd, hpc, hplt, hpne⟩ := (goodU_all u hu).2.1 h
      rw [show run (n+1) u = run n (parent u) by simp [run, h]]
      rw [← hpc]
      exact ih (parent u) hplt hpne (by omega)

private theorem cls_zero : cls 0 = 0 := by decide +kernel

private theorem dec_rep0 : dec (repCode 0) =
    TableBExc.redMod .E8 3 (TableBExcTwo.frameE8Root 0) := by
  decide +kernel

private theorem frameCoordHom_pi_single_zero :
    ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) =
      TableBExc.redMod .E8 3 (TableBExcTwo.frameE8Root 0) := by
  rw [ExcFrameIso.frameCoordHom_single]
  simp
  rfl

private theorem rep0_eq :
    dec (repCode 0) =
    ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) := by
  rw [frameCoordHom_pi_single_zero]
  exact dec_rep0

end M6cData

section M6c

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_torusAct_frameCoord_of_ncard_le (v : Fin Tag.E8.rank → ZMod 3) (hv : v ≠ 0)
    (h : Set.ncard {u : Fin Tag.E8.rank → ZMod 3 |
      ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w v} ≤ 240) :
    ∃ w : WeylGroup .E8,
      v = TableBExc.torusAct .E8 3 w (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8
          (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)) ∨
        v = -TableBExc.torusAct .E8 3 w (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8
          (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)) := by
  set u : Nat := enc v with hu
  have hu_lt : u < 6561 := enc_lt v
  have hdecv : dec u = v := by rw [hu, dec_enc]
  have hu_ne : u ≠ 0 := by
    intro h0
    apply hv
    rw [← hdecv, h0, dec_zero]
  set c : Nat := cls u with hc
  have hc_lt : c < 4 := cls_lt_four u
  by_cases hc0 : c = 0
  · refine ⟨(coxeterSystem .E8).wordProd (wordN (depth u) u), Or.inl ?_⟩
    have hdec : dec u = TableBExc.torusAct .E8 3
        ((coxeterSystem .E8).wordProd (wordN (depth u) u)) (dec (repCode c)) := by
      rw [dec_run (depth u) u, run_rep (depth u) u hu_lt hu_ne le_rfl]
    rw [← hdecv, hdec, hc0, rep0_eq]
  · exfalso
    have hc123 : c = 1 ∨ c = 2 ∨ c = 3 := by omega
    set S : Finset Nat := (Finset.range 6561).filter (fun x => cls x = c) with hS
    have hSge : 1920 ≤ S.card := lower_bound c hc123
    set wv : WeylGroup .E8 := (coxeterSystem .E8).wordProd (wordN (depth u) u) with hwv
    have hdecu : v = TableBExc.torusAct .E8 3 wv (dec (repCode c)) := by
      rw [hwv, ← hdecv, dec_run (depth u) u, run_rep (depth u) u hu_lt hu_ne le_rfl]
    have hrep : dec (repCode c) = TableBExc.torusAct .E8 3 wv⁻¹ v := by
      rw [hdecu, ← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
    have hxmem : ∀ x ∈ S, dec x ∈ {y : Fin Tag.E8.rank → ZMod 3 |
        ∃ w : WeylGroup .E8, y = TableBExc.torusAct .E8 3 w v} := by
      intro x hx
      have hxlt : x < 6561 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hxcl : cls x = c := (Finset.mem_filter.mp hx).2
      have hxne : x ≠ 0 := by
        intro h0
        rw [h0, cls_zero] at hxcl
        exact hc0 hxcl.symm
      refine ⟨((coxeterSystem .E8).wordProd (wordN (depth x) x)) * wv⁻¹, ?_⟩
      have hxdec : dec x = TableBExc.torusAct .E8 3
          ((coxeterSystem .E8).wordProd (wordN (depth x) x)) (dec (repCode c)) := by
        rw [dec_run (depth x) x, run_rep (depth x) x hxlt hxne le_rfl, hxcl]
      rw [hxdec, hrep, ← TableBExc.torusAct_mul]
    have hinj : Set.InjOn dec (↑S : Set Nat) := by
      intro x hx y hy hxy
      have hxlt : x < 6561 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hylt : y < 6561 := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      calc x = enc (dec x) := ((goodU_all x hxlt).2.2).symm
        _ = enc (dec y) := by rw [hxy]
        _ = y := (goodU_all y hylt).2.2
    have hle : S.card ≤ Set.ncard {y : Fin Tag.E8.rank → ZMod 3 |
        ∃ w : WeylGroup .E8, y = TableBExc.torusAct .E8 3 w v} := by
      have h1 := Set.ncard_le_ncard_of_injOn (s := (↑S : Set Nat))
        (t := {y : Fin Tag.E8.rank → ZMod 3 |
          ∃ w : WeylGroup .E8, y = TableBExc.torusAct .E8 3 w v})
        dec (fun x hx => hxmem x hx) hinj
      rwa [Set.ncard_coe_finset] at h1
    omega

end M6c

end CFSG.StandardType.FrameRoute.FS81

end
